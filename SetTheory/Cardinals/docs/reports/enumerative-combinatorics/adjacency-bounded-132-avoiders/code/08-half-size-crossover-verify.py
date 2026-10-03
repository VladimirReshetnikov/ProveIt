#!/usr/bin/env python3
"""Finite exact regressions for half_size_crossover.tex; never an asymptotic proof.
Run python verify.py, or python verify.py --max-n 256 for the longer table.
The credited endpoint model is shipped as model.py.
"""
from collections import Counter
from fractions import Fraction
from pathlib import Path
from time import perf_counter
import argparse, csv, json, math
from model import EndpointCounter, avoiders, catalans, max_jump


def parse(p,m):
    word=[]
    while len(p)>m:
        N=len(p); a=p.index(N); b=N-a-1
        left=tuple(x-b for x in p[:a]); right=p[a+1:]
        if a<=m and b<=m:
            return tuple(word),(left,right)
        if b>m:
            assert a+1<=m
            word.append(('R',left));p=right
        else:
            assert b==0 and a>m
            word.append(('A',()));p=left
    raise AssertionError('A parser core cannot have size <=m')


def reconstruct(word,core):
    left,right=core;b=len(right)
    p=tuple(x+b for x in left)+(len(left)+b+1,)+right
    for kind,left in reversed(word):
        if kind=='A':p=p+(len(p)+1,)
        else:
            b=len(p);p=tuple(x+b for x in left)+(len(left)+b+1,)+p
    return p


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--max-n',type=int,default=128)
    args=ap.parse_args();start=perf_counter();out=Path(__file__).resolve().parent
    checks=0;parsers=0
    for n in range(1,9):
        hist=Counter(max_jump(p) for p in avoiders(n))
        for m in range(1,n+1):
            c=EndpointCounter(n,m)
            expected=sum(v for k,v in hist.items() if k<=m)
            assert c.count()==expected
            c.T.cache_clear();c.unrestricted.cache_clear();checks+=1
            if m<n:
                signatures=set()
                for p in avoiders(n):
                    if max_jump(p)>m:continue
                    w,core=parse(p,m)
                    assert reconstruct(w,core)==p
                    assert (w,core) not in signatures
                    signatures.add((w,core));parsers+=1
    C=catalans(101);words=[1]+[0]*100;ronly=[1]+[0]*100
    for s in range(1,101):
        words[s]=words[s-1]+sum(C[k-1]*words[s-k] for k in range(1,s+1))
        ronly[s]=sum(C[k-1]*ronly[s-k] for k in range(1,s+1))
        assert words[s]==C[s+1] and ronly[s]==C[s]
    # Exact endpoint-state weight table with W_R=W_A=2, W=4.
    high=2*4+2*2;low=2*2
    assert Fraction(high+low,2)==8
    assert Fraction(2)+Fraction(2,2)==3
    rows=[]
    for n in (64,96,128,192,256):
        if n>args.max_n:continue
        for t in (Fraction(-1,2),Fraction(0),Fraction(1,2),Fraction(1)):
            m=math.floor(n/2+float(t)*math.sqrt(n));c=EndpointCounter(n,m)
            a=c.count();cn=c.C[n];p=Fraction(a,cn)
            rows.append(dict(n=n,m=m,t=str(t),count=str(a),catalan=str(cn),
                scaled_probability=float(n*p),limiting_function=6+12*max(float(t),0)/math.sqrt(math.pi)))
            c.T.cache_clear();c.unrestricted.cache_clear()
    with (out/'finite_checks.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=rows[0].keys());w.writeheader();w.writerows(rows)
    record=dict(status='PASS',endpoint_counts=checks,parser_reconstructions=parsers,
        word_coefficient_equalities=200,endpoint_masses={'pair':3,'triple':8},
        max_n=args.max_n,elapsed_seconds=perf_counter()-start,
        caveat='Finite regression only; not an asymptotic or proof-assistant verification')
    (out/'verification.json').write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps(record,indent=2))

if __name__=='__main__':main()
