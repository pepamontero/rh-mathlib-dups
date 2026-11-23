#!/usr/bin/env bash
# For each hit in a duplicates.csv, list the RH pull requests (open, merged and
# closed) that change the file the RH theorem lives in, and what each PR does
# to the theorem's declaration.
#
# Usage: dupfinder/check_prs.sh <duplicates.csv> [out.csv]
#
# Output columns:
#   rh_name,rh_module,pr,pr_state,pr_title,file_status,decl_at_pr_head
# file_status is GitHub's (modified, removed, ...) for the file. decl_at_pr_head
# compares the declaration text (first line to next blank line) at the PR head
# with main: "unchanged", "changed", "moved to <file>, unchanged/changed" (the
# PR moved it within the same directory, as bundling PRs do), "gone" (deleted,
# renamed, or moved elsewhere), or "not on main".
# "changed" or "gone" means the PR may already handle the hit: look at it.
# Hits no PR touches get one row with an empty pr column.
#
# Read-only against GitHub: only GET requests and git fetches. Needs gh, jq, git.
# File lists are cached per PR head commit in $PRCHECK_CACHE, so reruns only
# fetch PRs that changed. PRs whose API file list is incomplete (the API stops
# at 3000 files, sometimes fewer) are listed with a tree-only git diff instead.
set -euo pipefail

REPO=${RH_REPO:-leanprover-community/riemann-hypothesis}
CACHE=${PRCHECK_CACHE:-${XDG_CACHE_HOME:-$HOME/.cache}/rh-mathlib-dups/prcheck}

if [ $# -lt 1 ]; then
  echo "usage: $0 <duplicates.csv> [out.csv]" >&2
  exit 2
fi
in=$1
out=${2:-/dev/stdout}

mkdir -p "$CACHE/files"
G="$CACHE/git"
if [ ! -d "$G" ]; then
  git init -q "$G"
  git -C "$G" remote add origin "https://github.com/$REPO.git"
fi
fetch() { git -C "$G" fetch -q --filter=blob:none --depth=1 origin "$@"; }

# Hits: rh_name, rh_module, source path, short name of the declaration.
targets="$CACHE/targets.tsv"
tail -n +2 "$in" | awk -F, -v OFS='\t' 'NF >= 2 {
  path = $2; gsub(/\./, "/", path)
  n = split($1, parts, "."); print $1, $2, "src/" path ".lean", parts[n]
}' > "$targets"
echo "hits: $(wc -l < "$targets")" >&2

# All PRs: number, state (open/merged/closed), head sha, base sha, title.
gh api --paginate "repos/$REPO/pulls?state=all&per_page=100" --jq '.[] |
  [.number, (if .merged_at then "merged" else .state end), .head.sha, .base.sha,
   (.title | gsub("\t"; " "))] | @tsv' > "$CACHE/prs.tsv"
echo "PRs: $(wc -l < "$CACHE/prs.tsv")" >&2

# Changed-file list per PR (path <TAB> status), cached by head sha.
while IFS=$'\t' read -r num state head base title; do
  f="$CACHE/files/$num-$head.tsv"
  if [ -f "$f" ]; then continue; fi
  expected=$(gh api "repos/$REPO/pulls/$num" --jq '.changed_files')
  gh api --paginate "repos/$REPO/pulls/$num/files?per_page=100" \
    --jq '.[] | [.filename, .status] | @tsv' > "$f.tmp"
  listed=$(wc -l < "$f.tmp")
  if [ "$listed" -lt "$expected" ]; then
    echo "PR #$num: API listed $listed of $expected files, listing it with git" >&2
    mb=$(gh api "repos/$REPO/compare/$base...$head" --jq '.merge_base_commit.sha' 2>/dev/null || echo "$base")
    fetch "+refs/pull/$num/head:refs/pr/$num" "$mb"
    git -C "$G" diff-tree -r --no-renames --name-status "$mb" "refs/pr/$num" \
      | awk -F'\t' -v OFS='\t' '{
          s = ($1 == "D") ? "removed" : ($1 == "A") ? "added" : "modified"
          print $2, s }' > "$f.tmp"
  fi
  mv "$f.tmp" "$f"
done < "$CACHE/prs.tsv"

# Join hits with PR file lists.
matches="$CACHE/matches.tsv"
: > "$matches"
while IFS=$'\t' read -r num state head base title; do
  NUM=$num STATE=$state TITLE=$title awk -F'\t' -v OFS='\t' '
    NR == FNR { t[$3] = (t[$3] == "" ? "" : t[$3] "\n") $0; next }
    ($1 in t) {
      n = split(t[$1], rows, "\n")
      for (i = 1; i <= n; i++) print rows[i], ENVIRON["NUM"], ENVIRON["STATE"], ENVIRON["TITLE"], $2
    }' "$targets" "$CACHE/files/$num-$head.tsv" >> "$matches"
done < "$CACHE/prs.tsv"

# What does each matching PR do to the declaration itself? Fetch trees for
# main and those PR heads once; file contents are fetched on demand, one file
# (or, for a moved declaration, one directory) per match.
prs_needed=$(cut -f5 "$matches" | sort -un)
if [ -n "$prs_needed" ]; then
  refs=("+refs/heads/main:refs/remotes/origin/main")
  for n in $prs_needed; do refs+=("+refs/pull/$n/head:refs/pr/$n"); done
  fetch "${refs[@]}"
fi

# Text of a declaration: from its first line up to the next blank line.
# Usage: decl <ref> <path> <regex>
decl() {
  git -C "$G" cat-file -p "$1:$2" 2>/dev/null \
    | RE=$3 awk '$0 ~ ENVIRON["RE"] { p = 1 } p && /^[[:space:]]*$/ { exit } p' || true
}

csv() { local s=${1//\"/\"\"}; printf '"%s"' "$s"; }
{
  echo "rh_name,rh_module,pr,pr_state,pr_title,file_status,decl_at_pr_head"
  # open first, then merged, then closed; newest PR first within each.
  awk -F'\t' -v OFS='\t' '{ r = ($6 == "open") ? 0 : ($6 == "merged") ? 1 : 2; print r, $0 }' "$matches" \
    | sort -t$'\t' -k1,1n -k6,6nr | cut -f2- \
    | while IFS=$'\t' read -r name module path short num state title status; do
        re="^ *(@\[[^]]*\] *)?(private |protected )?(theorem|lemma) +([^ ]*\.)?$short([^[:alnum:]_'.]|$)"
        main_decl=$(decl origin/main "$path" "$re")
        head_decl=$(decl "refs/pr/$num" "$path" "$re")
        moved=""
        if [ -z "$head_decl" ]; then
          # Bundling PRs move declarations into another file of the same directory.
          other=$(git -C "$G" grep -l -E "$re" "refs/pr/$num" -- "${path%/*}/" 2>/dev/null | head -n 1 || true)
          other=${other#"refs/pr/$num:"}
          if [ -n "$other" ]; then
            head_decl=$(decl "refs/pr/$num" "$other" "$re")
            moved="moved to ${other##*/}, "
          fi
        fi
        if [ -z "$head_decl" ]; then
          effect=gone
        elif [ -z "$main_decl" ]; then
          effect="${moved}not on main"
        elif [ "$head_decl" = "$main_decl" ]; then
          effect="${moved}unchanged"
        else
          effect="${moved}changed"
        fi
        printf '%s,%s,%s,%s,%s,%s,%s\n' "$name" "$module" "$num" "$state" "$(csv "$title")" "$status" "$(csv "$effect")"
      done
  # hits that no PR touches
  awk -F'\t' 'NR == FNR { seen[$1] = 1; next } !($1 in seen) { print $1 "," $2 ",,,,," }' "$matches" "$targets"
} > "$out"
