#!/usr/bin/env python3
"""Check the bivariate component generating function against the saved counts.

Reads data/finite_verification.json (the exhaustive naturally labelled run) and
rebuilds its rank histograms from A(z)=1/(1-B(z)).  This is a consistency check
on saved counts, not an independent enumeration of posets.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("report", nargs="?", type=Path,
                        default=Path(__file__).resolve().parents[1] / "data/finite_verification.json")
    args = parser.parse_args()
    report = json.loads(args.report.read_text(encoding="utf-8"))
    rows = report["exhaustive"]
    nmax = len(rows)-1
    a = [row["naturally_labelled_posets"] for row in rows]
    if a[0] != 1 or any(row["n"] != n for n,row in enumerate(rows)):
        raise ValueError("Expected consecutive sizes starting from the empty poset")
    b = [0]*(nmax+1)
    for n in range(1,nmax+1):
        b[n] = a[n] - sum(b[i]*a[n-i] for i in range(1,n))
    f = [[0]*(nmax+1) for _ in range(nmax+1)]
    f[0][0] = 1
    for n in range(1,nmax+1):
        for m in range(1,n+1):
            for k in range(m-1,n+1):
                f[n][k] += b[m]*f[n-m][k-m+1]
    for n,row in enumerate(rows):
        expected = {str(k):count for k,count in enumerate(f[n]) if count}
        if expected != row["rank_histogram"]:
            raise AssertionError(f"Generating-function mismatch at size {n}")
    print(json.dumps({"status":"PASS", "maximum_n":nmax,
                      "connected_counts":b[1:],
                      "method":"A=1/(1-B), followed by weighted component convolution",
                      "limitation":"Consistency check on saved counts, not an independent poset enumeration"}, indent=2))


if __name__ == "__main__":
    main()
