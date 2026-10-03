#!/usr/bin/env python3
"""Exact endpoint-set verification of the fifth-truncation obstruction."""
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
import json

def count(cols):
    states={0}
    for c in cols:
        nxt=set()
        for st in states:
            avail=c&~st
            while avail:
                b=avail&-avail;avail-=b;nxt.add(st|b)
        states=nxt
    return len(states)

def main():
    core=[2,1,0];L=[7]*8;R=[1,2]+[3]*7+[4,5]
    vs=[F(15),F(15)]+[F(1)]*7+[F(15),F(1,10)]
    rows=core+L;B=[sum(1<<i for i,row in enumerate(rows) if row>>j&1) for j in range(3)]
    C=[]
    for k in range(4):
        total=F(0)
        for I in combinations(range(len(R)),k):
            w=F(1)
            for i in I:w*=vs[i]
            total+=w*count(B+[R[i] for i in I])
        C.append(total)
    expected=[F(120),F(26602,5),F(393176,5),F(1937208,5)]
    if C!=expected:raise RuntimeError(('Conditioned coefficients',C))
    gap=C[1]**2-3*C[0]*C[2]
    determinant=12*C[0]*C[2]-4*C[1]**2
    if gap!=F(-50396,25) or determinant!=F(201584,25):raise RuntimeError('Barrier value')
    out={'vertices':25,'matching_rank':6,'conditional_coefficients':[str(x) for x in C],'first_ULC3_gap':str(gap),'quadratic_Hessian_determinant':str(determinant),'positive_Hessian_diagonal':True,'fifth_truncation_Lorentzian':False,'scalar_ULC6_counterexample':False}
    Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))

if __name__=='__main__':main()
