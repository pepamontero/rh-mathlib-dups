#!/usr/bin/env python3
"""Markdown summary of a FindHomes CSV (homes.csv), for the workflow's job summary.

Usage: summarize_homes.py <homes.csv>
"""
import csv
import sys
from collections import Counter


def table(title, header, rows):
    print(f"### {title}")
    print()
    print("| " + " | ".join(header) + " |")
    print("|" + "---|" * len(header))
    for r in rows:
        print("| " + " | ".join(str(x) for x in r) + " |")
    print()


def main(path):
    with open(path, newline="") as f:
        rows = list(csv.DictReader(f))
    layer0 = [r for r in rows if r["layer"] == "0"]

    layers = Counter(min(int(r["layer"]), 10) for r in rows)
    table(
        f"{len(rows)} declarations by layer",
        ["layer", "declarations"],
        [("10+" if k == 10 else k, v) for k, v in sorted(layers.items())],
    )
    table(
        "By status",
        ["status", "declarations"],
        Counter(r["status"] for r in rows).most_common(),
    )
    table(
        f"Layer 0 by kind ({len(layer0)} declarations)",
        ["kind", "declarations"],
        Counter(r["kind"] for r in layer0).most_common(),
    )

    files = Counter(r["proposed_file"] for r in layer0 if r["proposed_file"])
    dirs = Counter("/".join(p.split("/")[:2]) for p in files.elements())
    table(
        f"Layer 0 by top-level ToMathlib folder ({len(files)} files in all)",
        ["folder", "declarations"],
        dirs.most_common(25),
    )
    table(
        "Largest proposed ToMathlib files",
        ["file", "declarations"],
        [(f"`{k}`", v) for k, v in files.most_common(30)],
    )

    # A layer-1 declaration only uses layer-0 ones, so these are the moves that
    # unblock the most of layer 1 (blocked_by lists at most 5 per declaration).
    unblock = Counter(
        b for r in rows if r["layer"] == "1" for b in r["blocked_by"].split(";") if b
    )
    table(
        "Layer-0 declarations that most layer-1 declarations wait on",
        ["declaration", "layer-1 users"],
        [(f"`{k}`", v) for k, v in unblock.most_common(20)],
    )


if __name__ == "__main__":
    main(sys.argv[1])
