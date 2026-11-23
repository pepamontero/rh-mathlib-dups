#!/usr/bin/env python3
"""Find where each Mathlib duplicate is declared and used in a riemann-hypothesis checkout.

Usage: find_callsites.py <duplicates.csv> <rh-checkout> [out-dir]

<duplicates.csv> is FindDups output. Generated equation lemmas (`foo.eq_1`, `foo.eq_def`) are
skipped: they are not in the source. <rh-checkout> needs every file of `src` but no build.
Writes to <out-dir> (default: callsites/):

  callsites.csv  one row per occurrence: rh_name, mathlib_name, file, line, verdict, token, text
  plan.md        per duplicate: where it is declared (with attributes) and what to edit
  files.txt      every file that needs editing (declarations and uses)

Text search can't resolve names the way Lean does, so every occurrence gets a verdict:
  definition  the declaration itself: delete it
  use         refers to the duplicate: the token is fully qualified, or the line is inside its
              namespace or after an `open` of it
  check       may refer to it: `.name` or `x.name` (dot notation), or bare in a file that opens a
              namespace ending like the duplicate's
  comment     inside a `--` comment or a doc comment
Bare or qualified occurrences that can't refer to the duplicate are counted, not listed.
Anything the search can't see (a `@[simp]` lemma used by `simp`, an instance found by instance
search) shows up only when the patch is compiled.
"""
import csv
import re
import subprocess
import sys
from collections import defaultdict
from pathlib import Path

EQN = re.compile(r"\.(eq_\d+|eq_def|eq_unfold)$")
DECL = re.compile(
    r"^\s*(?:@\[(?P<attr>[^\]]*)\]\s*)?"
    r"(?:(?:private|protected|noncomputable|nonrec|partial|unsafe|local|scoped)\s+)*"
    r"(?P<kw>theorem|lemma|instance|def|abbrev)\s+(?:\(priority\s*:=\s*\w+\)\s+)?(?P<name>[^\s:({\[]+)"
)
NS_OPEN = re.compile(r"^\s*namespace\s+(\S+)")
SECTION = re.compile(r"^\s*(?:noncomputable\s+)?section\b(?:\s+(\S+))?")
END = re.compile(r"^\s*end\b(?:\s+(\S+))?")
OPEN = re.compile(r"^\s*open\s+(?:scoped\s+)?([^(\n]*)")
# An instance without a name: Lean generates one (`instFactPrimeValNat_src`), which the source
# never spells out.
ANON_INSTANCE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|local|scoped)\s+)*"
    r"instance\s*(?:\(priority\s*:=\s*\w+\)\s*)?[:(\[{⦃]"
)


def is_ident(c):
    return c.isalnum() or c in "_'!?"


def tokens(line, short):
    """Positions and full dotted tokens where `short` occurs as a whole identifier component."""
    i = 0
    while (i := line.find(short, i)) != -1:
        j = i + len(short)
        before = line[i - 1] if i > 0 else " "
        after = line[j] if j < len(line) else " "
        if not is_ident(before) and not is_ident(after):
            k = i
            while k > 0 and (is_ident(line[k - 1]) or line[k - 1] == "."):
                k -= 1
            yield i, line[k:j]
        i = j


class FileInfo:
    """Namespace at each line, `open`s so far, and which lines are in comments."""

    def __init__(self, path):
        self.lines = path.read_text(errors="replace").splitlines()
        self.ns, self.in_doc = [], []
        self.open_events = []  # (line number, opened namespace)
        stack, doc = [], False
        for lno, line in enumerate(self.lines, 1):
            if m := NS_OPEN.match(line):
                stack.append(("ns", m.group(1)))
            elif m := SECTION.match(line):
                stack.append(("sec", m.group(1) or ""))
            elif (m := END.match(line)) and stack:
                stack.pop()
            if m := OPEN.match(line):
                cur = ".".join(n for k, n in stack if k == "ns")
                for o in m.group(1).split():
                    if o == "in":  # `open Foo in <command>`
                        break
                    self.open_events.append((lno, o))
                    if cur:
                        self.open_events.append((lno, cur + "." + o))
            starts_doc = "/-" in line
            self.in_doc.append(doc or starts_doc)
            if starts_doc and "-/" not in line.split("/-", 1)[1]:
                doc = True
            elif doc and "-/" in line:
                doc = False
            self.ns.append(".".join(n for k, n in stack if k == "ns"))

    def opens(self, lno):
        """Namespaces opened before line `lno` (ignoring the sections that scope them)."""
        return {o for l, o in self.open_events if l <= lno}


def in_scope(ns, at_ns, opens):
    """Is namespace `ns` visible unqualified: current namespace inside it, or opened."""
    return at_ns == ns or at_ns.startswith(ns + ".") or ns in opens


def main(dups, rh, out):
    rh, out = Path(rh), Path(out)
    out.mkdir(parents=True, exist_ok=True)
    hits = {}
    with open(dups, newline="") as f:
        for r in csv.DictReader(f):
            if EQN.search(r["rh_name"]):
                continue
            key = r["rh_name"]
            h = hits.setdefault(key, {"module": r["rh_module"], "mathlib": []})
            h["mathlib"].append((r["mathlib_name"], r["mathlib_module"]))
    for h in hits.values():
        # Prefer a Mathlib lemma over a core one when there are several.
        h["mathlib"].sort(key=lambda m: not m[1].startswith("Mathlib"))
    by_short = defaultdict(list)
    for name in hits:
        by_short[name.rsplit(".", 1)[-1]].append(name)

    cmd = ["git", "-C", str(rh), "-c", "core.quotePath=false", "grep", "-n", "-I", "-w", "-F"]
    for s in by_short:
        cmd += ["-e", s]
    cmd += ["--", "src"]
    res = subprocess.run(cmd, capture_output=True, text=True, errors="replace")
    if res.returncode > 1:
        sys.exit(res.stderr)

    files = {}

    def info(p):
        if p not in files:
            files[p] = FileInfo(rh / p)
        return files[p]

    # git grep lists matches file by file, so caching the current file's text is enough.
    current = {"path": None, "text": ""}

    def mentions(p, word):
        if current["path"] != p:
            current["path"], current["text"] = p, (rh / p).read_text(errors="replace")
        return word in current["text"]

    rows, unrelated = [], defaultdict(int)
    defs = defaultdict(list)
    for gl in res.stdout.splitlines():
        path, lno, text = gl.split(":", 2)
        lno = int(lno)
        for short, names in by_short.items():
            if short not in text:
                continue
            for pos, tok in tokens(text, short):
                for name in names:
                    ns = name.rsplit(".", 1)[0] if "." in name else ""
                    q = tok.lstrip(".")
                    # Unless the token spells out the full name, the file has to mention the
                    # duplicate's namespace somewhere (in a `namespace`, `open` or the token).
                    if ns and q != name and not mentions(path, ns.rsplit(".", 1)[-1]):
                        unrelated[name] += 1
                        continue
                    fi = info(path)
                    at_ns, opens = fi.ns[lno - 1], fi.opens(lno)
                    comment = "--" in text[:pos] or fi.in_doc[lno - 1]
                    d = DECL.match(text)
                    verdict = None
                    if d and d.group("name") == q and not comment:
                        full = (at_ns + "." + q) if at_ns and not q.startswith("_root_.") \
                            else q.removeprefix("_root_.")
                        if full == name:
                            verdict = "definition"
                            defs[name].append((path, lno))
                        else:
                            continue  # a different declaration with the same short name
                    elif tok.startswith("."):
                        verdict = "check"
                    elif q == short:
                        if in_scope(ns, at_ns, opens) or not ns:
                            verdict = "use"
                        elif any(o == ns or ns.endswith("." + o) for o in opens):
                            verdict = "check"
                    elif name == q or name.endswith("." + q):
                        head = name[: -len(q)].rstrip(".")
                        verdict = "use" if not head or in_scope(head, at_ns, opens) else "check"
                    elif q.split(".")[-2][:1].islower():
                        verdict = "check"  # `h.name`: dot notation on a term
                    if verdict is None:
                        unrelated[name] += 1
                        continue
                    if comment and verdict != "definition":
                        verdict = "comment"
                    rows.append([name, hits[name]["mathlib"][0][0], path, lno, verdict, tok,
                                 text.strip()[:200]])

    order = {"definition": 0, "use": 1, "check": 2, "comment": 3}
    rows.sort(key=lambda r: (r[0], order[r[4]], r[2], r[3]))
    with open(out / "callsites.csv", "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["rh_name", "mathlib_name", "file", "line", "verdict", "token", "text"])
        w.writerows(rows)
    edit_files = sorted({r[2] for r in rows if r[4] in ("definition", "use", "check")})
    (out / "files.txt").write_text("".join(p + "\n" for p in edit_files))

    per = defaultdict(list)
    for r in rows:
        per[r[0]].append(r)
    totals = defaultdict(int)
    with open(out / "plan.md", "w") as f:
        f.write("# Replacing Mathlib duplicates\n\n")
        f.write(f"Generated by `dupfinder/find_callsites.py` from `{Path(dups).name}`. "
                "Verdicts: see the script's docstring.\n\n")
        for name in sorted(hits):
            h = hits[name]
            m, mm = h["mathlib"][0]
            f.write(f"## `{name}`\n\nReplace with `{m}` (`{mm}`).\n")
            if len(h["mathlib"]) > 1:
                others = ", ".join(f"`{x}`" for x, _ in h["mathlib"][1:])
                f.write(f"Also equal to {others}.\n")
            f.write("\n")
            exp = "src/" + h["module"].replace(".", "/") + ".lean"
            if not defs[name] and (rh / exp).exists():
                anon = [i for i, line in enumerate(info(exp).lines, 1) if ANON_INSTANCE.match(line)]
                if anon:
                    f.write(f"* Not named in the source: probably the anonymous instance at "
                            + ", ".join(f"line {i}" for i in anon) + f" of `{exp}`.\n")
                    defs[name] = [(exp, i) for i in anon]
                    totals["anonymous instance"] += 1
            if not defs[name]:
                f.write(f"* **Declaration not found** (expected in `{exp}`). It may have moved "
                        "since the scan.\n")
                totals["not found"] += 1
            for path, lno in defs[name]:
                fi = info(path)
                start, end = lno, lno
                while start > 1 and fi.lines[start - 2].lstrip().startswith("@["):
                    start -= 1
                while end < len(fi.lines) and fi.lines[end].strip():
                    end += 1
                head = " ".join(fi.lines[start - 1:lno])
                flags = []
                if re.search(r"@\[[^\]]*\bsimp\b", head):
                    flags.append("`@[simp]`: removing it changes what `simp` does")
                if re.search(r"\binstance\b", head):
                    flags.append("instance: check the Mathlib instance is imported")
                if re.search(r"\blocal\s+instance\b", head):
                    flags.append("`local`: only this file relies on it")
                note = f" ({'; '.join(flags)})" if flags else ""
                f.write(f"* Declared in `{path}`, lines {start} to {end}{note}.\n")
            uses = [r for r in per[name] if r[4] != "definition"]
            for v in ("use", "check", "comment"):
                vs = [r for r in uses if r[4] == v]
                totals[v] += len(vs)
                if vs:
                    f.write(f"* {v} ({len(vs)}):\n")
                    seen = defaultdict(int)
                    for r in vs:
                        seen[(r[2], r[3], r[5])] += 1
                    for (p, l, t), k in seen.items():
                        times = f" ({k} times)" if k > 1 else ""
                        f.write(f"  * `{p}:{l}` `{t}`{times}\n")
            if not uses:
                f.write("* No uses found outside the declaration.\n")
            if unrelated[name]:
                f.write(f"* {unrelated[name]} occurrences of the short name ruled out.\n")
            f.write("\n")
    print(f"{len(hits)} duplicates, {len(edit_files)} files to edit; "
          + ", ".join(f"{k}: {v}" for k, v in sorted(totals.items()))
          + f"; ruled out: {sum(unrelated.values())}", file=sys.stderr)


if __name__ == "__main__":
    if len(sys.argv) not in (3, 4):
        sys.exit(__doc__)
    main(sys.argv[1], sys.argv[2], sys.argv[3] if len(sys.argv) == 4 else "callsites")
