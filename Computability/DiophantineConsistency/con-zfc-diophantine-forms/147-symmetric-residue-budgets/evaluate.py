#!/usr/bin/env python3
"""Exact evaluation, not a solver. JSON input is an ordered list of integers."""
import argparse,json
from pathlib import Path
ROOT=Path(__file__).resolve().parent

def value(terms,x):
    total=0
    for c,m in terms:
        term=c
        for i in m:term*=x[i]
        total+=term
    return total

def main():
    p=argparse.ArgumentParser();p.add_argument('point',type=Path);p.add_argument('--equation',choices=['P258','P261'],default='P258');a=p.parse_args()
    eq=json.loads((ROOT/'equations'/a.equation/'equation.json').read_text());x=json.loads(a.point.read_text())
    if not isinstance(x,list) or len(x)!=len(eq['variables']) or not all(type(v) is int for v in x):raise ValueError('Wrong coordinate count or non-integer coordinate')
    r=[value(t['terms'],x) for t in eq['residuals']]
    print(json.dumps({'equation':a.equation,'value':sum(t*t for t in r),'zero':all(t==0 for t in r)}))

if __name__=='__main__':main()
