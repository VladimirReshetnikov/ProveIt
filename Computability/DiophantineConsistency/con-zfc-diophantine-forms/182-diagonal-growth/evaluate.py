#!/usr/bin/env python3
"""Evaluate the literal quartic at a supplied integer tuple; no root search."""
import argparse
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parent

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('tuple',type=Path,help='JSON list of exactly 214 integers')
    p.add_argument('--modulus',type=int,help='optional positive modulus; modular zeros are not integer zeros')
    p.add_argument('--residuals',action='store_true')
    a=p.parse_args();x=json.loads(a.tuple.read_text())
    if type(x) is not list or len(x)!=214 or any(type(v) is not int for v in x):
        p.error('input must contain exactly 214 unrestricted integers')
    if a.modulus is not None and a.modulus<1:p.error('modulus must be positive')
    eq=json.loads((ROOT/'direct/diagonal214/equation.json').read_text())
    values=[]
    for row in eq['residuals']:
        total=0
        for coefficient,indices in row['terms']:
            term=coefficient
            for i in indices:term*=x[i]
            total+=term
        if a.modulus:total%=a.modulus
        values.append(total)
    result=sum(v*v for v in values)
    if a.modulus:result%=a.modulus
    out={'value':result,'modulus':a.modulus}
    if a.residuals:out['residuals']=values
    print(json.dumps(out))

if __name__=='__main__':main()
