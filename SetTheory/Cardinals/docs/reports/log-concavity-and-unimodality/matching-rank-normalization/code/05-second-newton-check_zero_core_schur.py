#!/usr/bin/env python3
from fractions import Fraction as F
from itertools import combinations
from random import Random
from pathlib import Path
import json

def states(cols):
    out={0}
    for col in cols:
        nxt=set()
        for s in out:
            a=col&~s
            while a:
                b=a&-a;a-=b;nxt.add(s|b)
        out=nxt
    return out
def count(cols):return len(states(cols))
def solve(A,b):
    n=len(b);X=[[F(v) for v in row]+[F(c)] for row,c in zip(A,b)]
    for i in range(n):
        k=next(k for k in range(i,n) if X[k][i]);X[i],X[k]=X[k],X[i]
        t=X[i][i];X[i]=[v/t for v in X[i]]
        for j in range(n):
            if i!=j:
                t=X[j][i];X[j]=[u-t*v for u,v in zip(X[j],X[i])]
    return [row[-1] for row in X]
def main():
    rng=Random(889);tested=0
    for C1 in range(8):
        for C2 in range(8):
            core=[((C1>>i)&1)*2+((C2>>i)&1)*4 for i in range(3)]
            L=[1,2,4]+[rng.randrange(1,8) for _ in range(5)]
            rows=core+L;B=[sum(1<<i for i,r in enumerate(rows) if r>>j&1) for j in range(3)]
            LB=[sum(1<<i for i,r in enumerate(L) if r>>j&1) for j in range(3)]
            n=LB[0].bit_count();p=[count([LB[0],LB[i]]) for i in [1,2]];q=count(LB)
            O=len(states([LB[0],LB[1]])&states([LB[0],LB[2]]));e=[C1.bit_count(),C2.bit_count()];c=(C1&C2).bit_count()
            rt=[1,2,3,4,5,6]
            pair=[count([B[0],r]) for r in rt]
            RR=[[F(4*pair[i]*pair[j],5*n)-count([B[0],rt[i],rt[j]]) for j in range(6)] for i in range(6)]
            x=[count([B[0],B[i]]) for i in [1,2]]
            cross=[[F(4*x[i]*pair[j],5*n)-count([B[0],B[i+1],rt[j]]) for j in range(6)] for i in range(2)]
            invcross=[solve(RR,b) for b in cross]
            S=[[F(4*x[i]*x[j],5*n)-(count(B) if i!=j else 0)-sum(cross[i][k]*invcross[j][k] for k in range(6)) for j in range(2)] for i in range(2)]
            target=[[F(p[i]**2,2*n)+2*e[i]*p[i]+n*e[i]*(e[i]-1)//2 if i==j else F(p[0]*p[1],2*n)-q+c*O for j in range(2)] for i in range(2)]
            if S!=target:raise RuntimeError((C1,C2,S,target))
            if S[0][0]*S[1][1]<S[0][1]**2:raise RuntimeError('Schur negative')
            tested+=1
    out={'core_column_pairs':tested,'exact_schur_identities':True,'all_pass':True};Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
