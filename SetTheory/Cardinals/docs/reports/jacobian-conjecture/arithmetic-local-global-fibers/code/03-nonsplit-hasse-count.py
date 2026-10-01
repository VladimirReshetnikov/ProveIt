"""Exact target counts, plus illustrative asymptotic ratios.

Run from any directory. The default table uses T=100,1000,10000,100000.
Examples:
  python code/count.py
  python code/count.py --heights 1000000 --output data/counts_large.json
The potentially expensive part is the O(T) split-root enumeration.
"""
from __future__ import annotations
import argparse
import json
import math
from pathlib import Path
from arithmetic import exact_counts


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--heights', nargs='+', type=int,
                        default=[100,1000,10000,100000])
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).resolve().parents[1]/'data'/'counts.json')
    args = parser.parse_args()
    if any(T < 2 for T in args.heights):
        parser.error('All heights must be >= 2, because the ratio uses log(T).')
    rows = []
    for T in args.heights:
        row = exact_counts(T)
        row['nonsplit_over_T_log_T'] = row['nonsplit_hasse']/(T*math.log(T))
        row['predicted_leading_constant'] = 27/(2*math.pi**2)
        row['integral_over_T_cuberoot'] = row['integral']/T**(1/3)
        rows.append(row)
        print(json.dumps(row),flush=True)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(rows,indent=2)+'\n')


if __name__ == '__main__':
    main()
