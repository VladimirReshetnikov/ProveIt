#!/usr/bin/env python3
"""Evaluate one of the fixed consistency polynomials at a supplied integer tuple."""
import argparse
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parent

def value(terms,point):
    total=0
    for coefficient,indices in terms:
        item=coefficient
        for i in indices:
            item*=point[i]
        total+=item
    return total

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('coordinates',type=Path,help='A JSON array of integers in the documented coordinate order.')
    parser.add_argument('--equation',choices=['direct306','matched1252','principal985','sparse1122'],
                        default='direct306')
    args=parser.parse_args()
    point=json.loads(args.coordinates.read_text())
    if not isinstance(point,list) or not all(type(x)is int for x in point):
        raise ValueError('Coordinates must be a JSON array of integers.')
    if args.equation=='direct306':
        source=json.loads((ROOT/'direct/integer306/equation.json').read_text())
        if len(point)!=len(source['variables']):
            raise ValueError('Expected 306 coordinates.')
        residuals=[value(r['terms'],point) for r in source['residuals']]
        result=sum(x*x for x in residuals)
        output={'equation':args.equation,'value':result,'is_zero':result==0,
                'nonzero_residuals':sum(x!=0 for x in residuals)}
    else:
        source=json.loads((ROOT/'graph'/args.equation/'polynomial.json').read_text())
        if len(point)!=len(source['variables']):
            raise ValueError('Incorrect coordinate count.')
        result=value(source['terms'],point)
        output={'equation':args.equation,'value':result,'is_zero':result==0}
    print(json.dumps(output,sort_keys=True))

if __name__=='__main__':
    main()
