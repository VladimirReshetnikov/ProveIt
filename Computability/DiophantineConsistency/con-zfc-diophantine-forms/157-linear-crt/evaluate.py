#!/usr/bin/env python3
"""Exactly evaluate a supplied integer tuple; this is not a root search."""
from pathlib import Path
import argparse,json,sys
ROOT=Path(__file__).resolve().parent
def evaluate(profile,point):
    equation=json.loads((ROOT/'equations'/profile/'equation.json').read_text())
    if not isinstance(point,list) or len(point)!=len(equation['variables']) or any(type(v) is not int for v in point):
        raise ValueError('Supply a JSON list of exactly '+str(len(equation['variables']))+' integers')
    values=[]
    for row in equation['residuals']:
        total=0
        for coefficient,monomial in row['terms']:
            term=coefficient
            for index in monomial:term*=point[index]
            total+=term
        values.append(total)
    result=sum(r*r for r in values)
    return {'profile':profile,'value':result,'is_zero':result==0,'nonzero_residuals':sum(r!=0 for r in values)}
if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('point',help='JSON file, or - for standard input')
    p.add_argument('--profile',choices=['P238','P239_sparse','P239_low_height'],default='P238')
    args=p.parse_args();point=json.load(sys.stdin) if args.point=='-' else json.loads(Path(args.point).read_text())
    print(json.dumps(evaluate(args.profile,point),indent=2))
