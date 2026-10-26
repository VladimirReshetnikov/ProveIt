#!/usr/bin/env python3
"""Evaluate the complete quartic at a user-supplied integer tuple."""
from pathlib import Path
import argparse,json
ROOT=Path(__file__).resolve().parent
def main():
    ap=argparse.ArgumentParser();ap.add_argument('tuple',type=Path);ap.add_argument('--modulus',type=int)
    args=ap.parse_args();point=json.loads(args.tuple.read_text())
    e=json.loads((ROOT/'equations/principal208/equation.json').read_text())
    if not isinstance(point,list) or len(point)!=208 or any(type(v) is not int for v in point):raise ValueError('Expected a JSON list of 208 integers')
    if args.modulus is not None and args.modulus<2:raise ValueError('Modulus must be at least two')
    rs=[]
    for row in e['residuals']:
        value=0
        for c,m in row['terms']:
            v=c
            for i in m:v*=point[i]
            value+=v
        rs.append(value if args.modulus is None else value%args.modulus)
    result=sum(v*v for v in rs)
    if args.modulus is not None:result%=args.modulus
    print(json.dumps({'polynomial_value':result,'modulus':args.modulus}))
if __name__=='__main__':main()
