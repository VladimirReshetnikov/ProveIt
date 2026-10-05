#!/usr/bin/env python3
from pathlib import Path
from itertools import combinations,permutations
import sympy as s,json,time
from functools import lru_cache
ROOT=Path(__file__).resolve().parent
A,B,C,P=s.symbols('a b c p',positive=True)

def count(cols):
    out={0}
    for c in cols:out={a|(1<<i) for a in out for i in range(3) if c>>i&1 and not a>>i&1}
    return len(out)

def perm(mask,p):return sum(1<<p[i] for i in range(3) if mask>>i&1)
def canonical(pair):return min(tuple(sorted(perm(x,p) for x in pair)) for p in permutations(range(3)))
def block(J,K):
    E=P+A*K.bit_count()+B*J.bit_count()+C*(J|K).bit_count()+count([J,K])
    r=s.Matrix([P*S.bit_count()+A*count([K,S])+B*count([J,S])+C*count([J|K,S])+count([J,K,S]) for S in range(1,8)])
    h=s.Matrix(7,7,lambda i,j:P*count([i+1,j+1])+A*count([K,i+1,j+1])+B*count([J,i+1,j+1])+C*count([J|K,i+1,j+1]))
    return E,r,3*r*r.T-4*E*h

def main():
    import argparse
    ap=argparse.ArgumentParser();ap.add_argument('J',type=int);ap.add_argument('K',type=int);args=ap.parse_args();J,K=args.J,args.K
    start=time.time();E,r,H=block(J,K)
    pivots=list(H.subs({A:2,B:3,C:4,P:32}).rref()[1]);H=H.extract(pivots,pivots)
    inv=H.inv(method='DM');det=s.factor(H.det(method='domain-ge'))
    out={'pair':[J,K],'pivots':pivots,'E':str(E),'determinant':str(det),'inverse':[[str(s.factor(z)) for z in row] for row in inv.tolist()],'seconds':time.time()-start}
    (ROOT/f'BB_R_{J}_{K}.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='inverse'},indent=2),flush=True)
if __name__=='__main__':main()
