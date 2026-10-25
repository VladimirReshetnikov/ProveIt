#!/usr/bin/env python3
"""Evaluate a selected quartic exactly; this is not a consistency solver."""
import argparse,json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]

def main():
    config=json.loads((ROOT/'ENDPOINTS.json').read_text())
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('point',type=Path,help='JSON list in the delivered coordinate order')
    ap.add_argument('--profile',choices=list(config['selected']),default=config['primary'])
    args=ap.parse_args()
    equation=json.loads((ROOT/config['selected'][args.profile]['path']/'equation.json').read_text())
    point=json.loads(args.point.read_text())
    if not isinstance(point,list) or len(point)!=len(equation['variables']) or any(type(x)is not int for x in point):
        raise ValueError('supply exactly the required number of unrestricted integers')
    values=[]
    for row in equation['residuals']:
        value=0
        for coefficient,indices in row['terms']:
            product=coefficient
            for i in indices:product*=point[i]
            value+=product
        values.append(value)
    print(json.dumps({'profile':args.profile,'value':sum(x*x for x in values),'zero':all(x==0 for x in values),'residuals':values}))

if __name__=='__main__':main()
