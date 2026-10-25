#!/usr/bin/env python3
"""Evaluate one literal direct polynomial at a supplied integer tuple."""
from pathlib import Path
import argparse,json
ROOT=Path(__file__).resolve().parent.parent
def main():
    p=argparse.ArgumentParser();p.add_argument('endpoint',choices=['self_power235','self_power236','shared_error234']);p.add_argument('tuple',type=Path);a=p.parse_args()
    e=json.loads((ROOT/'equations'/a.endpoint/'equation.json').read_text());x=json.loads(a.tuple.read_text())
    if len(x)!=len(e['variables']) or not all(type(v)is int for v in x):raise ValueError('wrong number or type of integer coordinates')
    residuals=[]
    for r in e['residuals']:
        s=0
        for c,m in r['terms']:
            z=c
            for i in m:z*=x[i]
            s+=z
        residuals.append(s)
    print(json.dumps({'endpoint':a.endpoint,'value':sum(r*r for r in residuals),'all_residuals_zero':all(r==0 for r in residuals)}))
if __name__=='__main__':main()
