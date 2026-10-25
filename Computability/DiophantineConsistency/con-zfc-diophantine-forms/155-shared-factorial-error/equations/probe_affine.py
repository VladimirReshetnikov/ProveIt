#!/usr/bin/env python3
"""Exact sparse elimination of quadratic parts, used only to find certificates."""
from fractions import Fraction
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parent
def add_scaled(a,b,k):
    for j,c in b.items():
        a[j]=a.get(j,Fraction(0))+k*c
        if not a[j]:del a[j]
def kernel(eq):
    basis={};dependencies=[]
    for i,r in enumerate(eq['residuals']):
        p={tuple(m):Fraction(c) for c,m in r['terms'] if len(m)==2};c={i:Fraction(1)}
        while p:
            m=min(p)
            if m not in basis:
                k=p[m];p={t:v/k for t,v in p.items()};c={t:v/k for t,v in c.items()};basis[m]=(p,c);break
            q,d=basis[m];k=p[m];add_scaled(p,q,-k);add_scaled(c,d,-k)
        if not p:dependencies.append(c)
    return dependencies,len(basis)
def main():
    e=json.loads((ROOT/'candidate245/equation.json').read_text());ds,rank=kernel(e)
    print('rank',rank,'dependencies',len(ds))
    for c in ds:
        p={}
        for i,k in c.items():add_scaled(p,{tuple(m):Fraction(v) for v,m in e['residuals'][i]['terms']},k)
        print('combination',[(i,str(k)) for i,k in c.items()])
        print('affine',[(str(k),[(v,e['variables'][v]['name']) for v in m]) for m,k in p.items()])
if __name__=='__main__':main()
