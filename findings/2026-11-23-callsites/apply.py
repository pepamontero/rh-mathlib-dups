#!/usr/bin/env python3
"""Replace the Mathlib duplicates of 2026-11-23 in a riemann-hypothesis checkout.

Usage: apply.py <rh-checkout>    (run from the rh-mathlib-dups repo root)

Reads callsites.csv next to this file. For each duplicate not in KEEP: every listed use is
rewritten to the Mathlib lemma (with the argument fixes in FIX), then the declaration is deleted
together with its attributes and doc comment. Edits files in place; review with `git diff`.
"""
import csv
import re
import sys
from collections import defaultdict
from pathlib import Path

HERE = Path(__file__).parent

# Duplicates to leave alone, by short name.
KEEP = {
    # Mathlib only has these as `local instance` (instFactPrimeValNat, Polynomial.instTwoPiPos),
    # so outside their own file they are not instances: the RH copies are needed.
    "instFactPrimeValNat_src", "instFactPrimeValNat_development", "factPrimes",
    "factTwoPi", "factTwoPiPos",
    # The Mathlib lemmas are deprecated.
    "isPrime_span_X",          # PowerSeries.span_X_isPrime
    "isUnit_of_sub_one_mem",   # Ideal.isUnit_of_sub_one_mem_jacobson_bot
}

# Where the arguments differ: (regex on the use line after renaming, replacement).
FIX = {
    # Mathlib takes `n` explicitly; `rw [...]` doesn't mind, a function argument does.
    "nsmul_zmod": [(r"(\(X := Y\) )ZModModule\.char_nsmul_eq_zero\b(?! n)",
                    r"\1(ZModModule.char_nsmul_eq_zero n)")],
    # Mathlib takes the prime `p` explicitly; RH callers pass `(l := l)`.
    "exists_zpow_neg_lt": [(r"PadicInt\.exists_pow_neg_lt \(l := l\)", "PadicInt.exists_pow_neg_lt (p := l)")],
    "exists_pow_lt": [(r"PadicInt\.exists_pow_neg_lt \(l := l\)", "PadicInt.exists_pow_neg_lt (p := l)")],
    # Mathlib takes `m n` explicitly.
    "castAdd_inj'": [(r"Fin\.castAdd_injective\b(?! _ _)", "(Fin.castAdd_injective _ _)")],
    # RH took `x` explicitly, Mathlib implicitly.
    "posLog_nonneg'": [(r"Real\.posLog_nonneg _", "Real.posLog_nonneg")],
    "abs_sin_eq": [(r"Real\.abs_sin_eq_sin_abs_of_abs_le_pi _ ", "Real.abs_sin_eq_sin_abs_of_abs_le_pi ")],
    # Named arguments whose name differs.
    "norm_l_lt_one": [(r"Padic\.norm_p_lt_one \(l := ", "Padic.norm_p_lt_one (p := ")],
    "exists_exp_neg_lt": [(r"WithZero\.exists_exp_neg_natCast_lt \(γ := ",
                           "WithZero.exists_exp_neg_natCast_lt (x := ")],
    # The file has `open PowerSeries`, and the RH proof of `hs` used this short form.
    "hs": [(r"PowerSeries\.HasSubst\.of_constantCoeff_zero'", "HasSubst.of_constantCoeff_zero'")],
}

# Imports to add: (file, line to add after the last `public import`).
IMPORTS = {
    # Mathlib's `IsNonarchimedeanLocalField ℚ_[p]` instance, replacing the RH one; public so
    # that files downstream still find it.
    "src/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PadicIsNonarchimedeanLocalField.lean":
        "public import Mathlib.NumberTheory.Padics.LocalField",
}


def is_ident(c):
    return c.isalnum() or c in "_'!?"


def replace_token(line, tok, new):
    """Replace whole-identifier occurrences of the dotted token `tok`."""
    out, i = [], 0
    while (j := line.find(tok, i)) != -1:
        k = j + len(tok)
        before = line[j - 1] if j else " "
        after = line[k] if k < len(line) else " "
        if not (is_ident(before) or before == ".") and not is_ident(after):
            out.append(line[i:j] + new)
        else:
            out.append(line[i:k])
        i = k
    out.append(line[i:])
    return "".join(out)


def decl_range(lines, i):
    """Lines [s, e) of the declaration starting at index i: attributes and doc comment above it,
    everything down to the next blank line."""
    s = i
    while s > 0 and lines[s - 1].lstrip().startswith("@["):
        s -= 1
    if s > 0 and lines[s - 1].rstrip().endswith("-/"):
        j = s - 1
        while j >= 0 and "/-" not in lines[j]:
            j -= 1
        if j >= 0 and "/--" in lines[j]:
            s = j
    e = i + 1
    while e < len(lines) and lines[e].strip():
        e += 1
    return s, e


def main(rh):
    rh = Path(rh)
    rows = [r for r in csv.DictReader(open(HERE / "callsites.csv"))
            if r["verdict"] in ("definition", "use")
            and r["rh_name"].rsplit(".", 1)[-1] not in KEEP]
    files = defaultdict(list)
    for r in rows:
        files[r["file"]].append(r)
    for path, rs in sorted(files.items()):
        p = rh / path
        lines = p.read_text().split("\n")
        # 1. Rename uses (line numbers don't move). A line with several occurrences has several
        # rows; the first one rewrites them all.
        done = set()
        for r in rs:
            if r["verdict"] != "use" or (r["line"], r["token"]) in done:
                continue
            done.add((r["line"], r["token"]))
            i = int(r["line"]) - 1
            short = r["rh_name"].rsplit(".", 1)[-1]
            new = replace_token(lines[i], r["token"], r["mathlib_name"])
            for pat, rep in FIX.get(short, []):
                new = re.sub(pat, rep, new)
            if new == lines[i]:
                sys.exit(f"{path}:{r['line']}: `{r['token']}` not found")
            lines[i] = new
        # 2. Delete declarations, bottom up, with the blank line after them.
        defs = sorted((int(r["line"]) - 1 for r in rs if r["verdict"] == "definition"), reverse=True)
        for i in defs:
            s, e = decl_range(lines, i)
            if e < len(lines) and not lines[e].strip() and (s == 0 or not lines[s - 1].strip()):
                e += 1
            del lines[s:e]
        # 3. Imports.
        if path in IMPORTS:
            last = max(k for k, line in enumerate(lines) if line.startswith("public import"))
            lines.insert(last + 1, IMPORTS[path])
        p.write_text("\n".join(lines))
    print(f"edited {len(files)} files", file=sys.stderr)


if __name__ == "__main__":
    if len(sys.argv) != 2:
        sys.exit(__doc__)
    main(sys.argv[1])
