#!/usr/bin/env python3
"""Reproduce the targeted CRT search; no claim of global minimality.

Only candidates a_c < 10^(c-3) can yield the targeted length failure when the
exact 5-adic valuation is c. Every hit is tested with its ACTUAL valuations.
"""
from __future__ import annotations
import argparse
import json
import sys
from pathlib import Path
from tetration_tools import Profile, crt_base


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-c', type=int, default=2547)
    parser.add_argument('--output', type=Path, default=Path('search_results.json'))
    args = parser.parse_args()
    if args.max_c < 4:
        parser.error('--max-c must be at least 4')
    if hasattr(sys, 'set_int_max_str_digits'):
        sys.set_int_max_str_digits(max(100000, 2*args.max_c))
    hits, failures = [], []
    for c in range(4,args.max_c+1):
        a = crt_base(c)
        if a >= 10**(c-3):
            continue
        p = Profile.from_base(a)
        digits = len(str(a))
        b = digits+2
        row = {
            'crt_parameter': c, 'digits': digits,
            'alpha': p.alpha, 'beta': p.beta, 'actual_c': p.c,
            'conjectured_height': b, 'speed_at_bound': p.speed(b),
            'eventual_speed': p.eventual_speed, 'exact_onset': p.onset,
            'is_counterexample': p.speed(b) != p.eventual_speed,
        }
        hits.append(row)
        if row['is_counterexample']:
            failures.append(c)
    result = {
        'search_interval_inclusive': [4,args.max_c],
        'candidates_examined': args.max_c-3,
        'filter': 'a_c < 10^(c-3)', 'length_deficit_hits': hits,
        'counterexample_parameters': failures,
        'scope': 'Targeted CRT-family search only; not an exhaustive search over all integer bases.'
    }
    args.output.write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()
