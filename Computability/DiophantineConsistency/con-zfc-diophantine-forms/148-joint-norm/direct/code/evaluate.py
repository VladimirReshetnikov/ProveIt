#!/usr/bin/env python3
"""Exactly evaluate the displayed quartic at an ordered integer tuple."""
from pathlib import Path
import argparse
import json

ROOT=Path(__file__).resolve().parents[1]


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('point',type=Path,help='JSON array of 245 integers')
    args=ap.parse_args()
    equation=json.loads((ROOT/'equation/equation.json').read_text())
    point=json.loads(args.point.read_text())
    if not isinstance(point,list) or len(point)!=len(equation['variables']) or any(type(x) is not int for x in point):
        raise ValueError('Expected an ordered JSON array of 245 integers')
    rows=[]
    for row in equation['residuals']:
        value=0
        for coefficient,monomial in row['terms']:
            term=coefficient
            for index in monomial:
                term*=point[index]
            value+=term
        rows.append(value)
    value=sum(x*x for x in rows)
    print(json.dumps({'polynomial_value':value,'is_zero':value==0,
                      'nonzero_residuals':sum(x!=0 for x in rows)},indent=2))


if __name__=='__main__':
    main()
