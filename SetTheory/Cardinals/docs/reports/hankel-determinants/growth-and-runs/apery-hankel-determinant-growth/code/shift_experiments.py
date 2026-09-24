#!/usr/bin/env python3
"""Exact sample determinants with a shift proportional to matrix index.

Without --gmp, uses the standard-library Python implementation. The defaults
are deliberately small. The delivered larger run used --indices 10,20,40,80.
For each row, r is fixed across that matrix; it is not varied with i or j.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import subprocess
from apery_exact import apery_hankel

ROOT = Path(__file__).resolve().parents[1]


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--gmp", type=Path, help="path to compiled apery_gmp executable")
    p.add_argument("--indices", default="10,20")
    p.add_argument("--output", type=Path, default=ROOT/"data/shift_experiments.json")
    args = p.parse_args()
    indices = [int(x) for x in args.indices.split(",")]
    if any(n < 1 for n in indices):
        p.error("indices must be positive")
    rows = []
    # (m, rho), with integral rho so r=rho*n exactly.
    for m, rho in [(1,1), (2,0), (2,1)]:
        for n in indices:
            r = rho*n
            if args.gmp is None:
                d = apery_hankel(n, stride=m, shift=r)[-1]
            else:
                run = subprocess.run([str(args.gmp.resolve()),str(n),str(m),str(r)],
                                     text=True, capture_output=True, check=True)
                records = [line.split() for line in run.stdout.splitlines()
                           if line and not line.startswith("#")]
                if int(records[-1][0]) != n:
                    raise RuntimeError("incomplete GMP output")
                d = int(records[-1][1])
            # Independent implementation cross-check on small samples.
            crosschecked = n <= 20
            if crosschecked and d != apery_hankel(n, stride=m, shift=r)[-1]:
                raise ArithmeticError("GMP/Python shift disagreement")
            rows.append({"n":n,"stride":m,"shift":r,"rho":rho,
                         "exact_determinant":str(d),
                         "crosschecked_with_python":crosschecked})
            print(f"completed m={m}, r={r}, n={n}", flush=True)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps({"rows":rows},indent=2)+"\n",encoding="utf-8")


if __name__ == "__main__":
    main()
