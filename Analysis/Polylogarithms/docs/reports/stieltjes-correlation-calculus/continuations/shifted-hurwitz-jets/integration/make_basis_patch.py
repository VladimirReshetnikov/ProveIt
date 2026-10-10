#!/usr/bin/env python3
"""Generate (but do not apply) the guarded search-basket wording patch."""
from __future__ import annotations
import argparse, difflib
from pathlib import Path

REL = Path("Analysis/Polylogarithms/docs/manuscript/chapters/07-integration.tex")
OLD = "Basis atoms must be\n$\\mathbb{Q}$-independent."
NEW = ("Remove or quotient known dependencies in the search basket, and distinguish\n"
       "relations involving the target from pre-existing relations among the basket\n"
       "atoms. Unknown numerical independence is not a prerequisite for an exact proof.")

def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--repo", required=True, type=Path)
    p.add_argument("--output", type=Path)
    args = p.parse_args()
    source = args.repo / REL
    text = source.read_text(encoding="utf-8")
    if text.count(OLD) != 1:
        raise SystemExit("Expected source sentence was not found exactly once. Refresh and reconcile the source.")
    revised = text.replace(OLD, NEW)
    diff = "".join(difflib.unified_diff(
        text.splitlines(keepends=True), revised.splitlines(keepends=True),
        fromfile="a/" + REL.as_posix(), tofile="b/" + REL.as_posix()))
    if args.output:
        args.output.write_text(diff, encoding="utf-8")
        print(f"Wrote {args.output}; the checkout is unchanged.")
    else:
        print(diff, end="")

if __name__ == "__main__":
    main()
