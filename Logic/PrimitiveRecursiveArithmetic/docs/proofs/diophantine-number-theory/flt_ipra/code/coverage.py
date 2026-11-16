#!/usr/bin/env python3
"""Exact description of the exponent family proved in the accompanying paper.

This is a family enumerator, not an FLT proof checker. An omitted exponent
means only that this package does not supply its proof.
"""
import argparse
import csv
import json
from pathlib import Path

BASES = (3, 4, 5, 7)
PERIOD = 420


def reduction(n):
    if n < 3:
        return None
    for d in BASES:
        if n % d == 0:
            return d, n // d
    return None


def report(limit):
    residues = [n for n in range(PERIOD) if any(n % d == 0 for d in BASES)]
    covered = [n for n in range(3, limit + 1) if reduction(n)]
    outside = [n for n in range(3, limit + 1) if not reduction(n)]
    assert len(residues) == 276
    return {
        "base_exponents": BASES,
        "period": PERIOD,
        "covered_residue_count": len(residues),
        "density_exact": "23/35",
        "limit": limit,
        "covered": covered,
        "not_established_by_this_package": outside,
    }


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--limit", type=int, default=200)
    ap.add_argument("--csv", type=Path)
    ap.add_argument("--json", type=Path)
    args = ap.parse_args()
    result = report(args.limit)
    if args.csv:
        with args.csv.open("w", newline="") as f:
            w = csv.writer(f)
            w.writerow(("exponent", "status", "base", "multiplier"))
            for n in range(3, args.limit + 1):
                r = reduction(n)
                w.writerow((n, "proved" if r else "not established here",
                            r[0] if r else "", r[1] if r else ""))
    text = json.dumps(result, indent=2) + "\n"
    if args.json:
        args.json.write_text(text)
    else:
        print(text, end="")


if __name__ == "__main__":
    main()
