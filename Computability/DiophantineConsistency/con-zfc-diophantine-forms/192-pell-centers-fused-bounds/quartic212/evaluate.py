#!/usr/bin/env python3
"""Evaluate a supplied integer tuple. This program performs no root search."""
from pathlib import Path
import argparse,json
ROOT=Path(__file__).resolve().parent
def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('tuple',type=Path)
    p.add_argument('--profile',choices=['reduced','equation'],default='reduced')
    p.add_argument('--modulus',type=int)
    a=p.parse_args();xs=json.loads(a.tuple.read_text())
    if not isinstance(xs,list) or len(xs)!=212 or any(type(x) is not int for x in xs):
        raise ValueError('Expected exactly 212 unrestricted integers')
    if a.modulus is not None and a.modulus<2:raise ValueError('Modulus must be at least two')
    e=json.loads((ROOT/a.profile/'equation.json').read_bytes());values=[]
    for r in e['residuals']:
        v=0
        for c,m in r['terms']:
            t=c
            for i in m:t*=xs[i]
            v+=t
        values.append(v if a.modulus is None else v%a.modulus)
    result=sum(v*v for v in values)
    if a.modulus:result%=a.modulus
    print(json.dumps({'profile':a.profile,'value':result,'modulus':a.modulus}))
if __name__=='__main__':main()
