#!/usr/bin/env python3
"""Construct an exact real order filter at an integer order center.

Examples:
    python code/design_filter.py joint 3
    python code/design_filter.py jump 2 --output replay/filter.json
    python code/design_filter.py completion 4

'joint' cancels both data at the first N actions, with minimum degree 2N.
'jump' cancels the jump at the first N actions, degree N+1, normalized by
cos(pi D) Pi(0)=1. 'completion' cancels the arithmetic completion at those
actions, degree N. The formulas are exact symbolic expressions.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import sympy as sp
from verify import U, P, invert, trig


def design(kind: str, depth: int) -> dict[str, str | int]:
    if depth < 1:
        raise ValueError('depth must be a positive integer')
    q = sp.prod(U + sp.log(n) for n in range(1, depth + 1))
    if kind == 'joint':
        poly = sp.prod((U + sp.log(n))**2 + P**2 for n in range(1, depth + 1))
    elif kind == 'jump':
        poly = invert(q, 'sin', normalize=True)
    elif kind == 'completion':
        poly = invert(q, 'cos')
    else:
        raise ValueError('kind must be joint, jump, or completion')
    out = poly.subs(P, sp.pi)
    return {'kind': kind, 'depth': depth, 'degree': int(sp.degree(poly, U)),
            'polynomial': str(out), 'latex': sp.latex(out),
            'real_part_polynomial': str(trig(poly, 'cos').subs(P, sp.pi)),
            'imaginary_part_polynomial': str(trig(poly, 'sin').subs(P, sp.pi)),
            'scope': 'integer center; joint filter also works at every real center'}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('kind', choices=['joint', 'jump', 'completion'])
    parser.add_argument('depth', type=int)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--overwrite', action='store_true')
    args = parser.parse_args()
    if args.depth < 1:
        parser.error('depth must be positive')
    if args.output and args.output.exists() and not args.overwrite:
        parser.error('output exists; choose another path or explicitly use --overwrite')
    text = json.dumps(design(args.kind, args.depth), indent=2) + '\n'
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding='utf-8')
    else:
        print(text, end='')


if __name__ == '__main__':
    main()
