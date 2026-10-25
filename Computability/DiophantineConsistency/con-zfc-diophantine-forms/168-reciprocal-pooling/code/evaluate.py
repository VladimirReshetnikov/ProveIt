#!/usr/bin/env python3
"""Evaluate one specified integer tuple; this is not a solvability test."""
import argparse
import json
from pathlib import Path
import sys

ROOT=Path(__file__).resolve().parents[1]


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('profile',choices=['quartic218','decic215'])
    ap.add_argument('point',help='JSON file containing an integer list, or - for stdin')
    ap.add_argument('--residuals',action='store_true')
    args=ap.parse_args()
    eq=json.loads((ROOT/'equations'/args.profile/'equation.json').read_text())
    point=json.load(sys.stdin) if args.point=='-' else json.loads(Path(args.point).read_text())
    if not isinstance(point,list) or len(point)!=len(eq['variables']) or any(type(x) is not int for x in point):
        ap.error(f"Expected exactly {len(eq['variables'])} integers (booleans are not integers here)")
    values=[]
    for row in eq['residuals']:
        result=0
        for c,indices in row['terms']:
            term=c
            for index in indices:term*=point[index]
            result+=term
        values.append(result)
    if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(0)
    result={'profile':args.profile,'value':sum(x*x for x in values)}
    if args.residuals:result['residuals']=values
    print(json.dumps(result))


if __name__=='__main__':main()
