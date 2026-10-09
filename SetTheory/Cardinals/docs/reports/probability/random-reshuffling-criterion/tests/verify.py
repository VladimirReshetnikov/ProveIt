#!/usr/bin/env python3
"""Deterministic exact checks; no Monte Carlo assertions and no tolerances.
Run from package root: python tests/verify.py
"""
from __future__ import annotations
import sys,json,random,time,platform
from pathlib import Path
from fractions import Fraction as F
from math import comb
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'code'))
from exact_matrices import *
from classify import classify,serialize
import sympy as s

assertions=0

def check(condition,message):
    global assertions
    assertions+=1
    if not condition: raise AssertionError(message)

def projected(a,rows,cols):
    return tuple(tuple(a[i][j] for j in cols) for i in rows)

def scalar_sym(expr):
    return s.factor(expr)

def main():
    start=time.perf_counter();rng=random.Random(20261008)
    fixtures=0;direct=0;coefficient_checks=0
    # Include both zero-variance and full-rank-variance behavior.
    for n in range(2,7):
        for d,r in [(2,1),(3,1),(3,2)]:
            raw=[]
            for _ in range(n-1):
                a=[[0]*d for _ in range(d)]
                for i in range(r):
                    for j in range(i,r): a[i][j]=a[j][i]=rng.randrange(-2,3)
                raw.append(matrix(a))
            last=zeros(d)
            for a in raw: last=sub(last,a)
            ds=tuple(raw+[last])
            H=matrix([[100 if i==j else (1 if abs(i-j)==1 else 0) for j in range(d)] for i in range(d)])
            hs=tuple(add(H,a) for a in ds)
            h,v,_=moments(hs)
            K=tuple(range(r,d)); allrows=tuple(range(d))
            for m in range(2,n+1):
                for mode in ['constant','unequal']:
                    ws=tuple(F(1) if mode=='constant' else F(1+(j*2+m)%5,1+j%2) for j in range(m))
                    wr,rr=expectations(hs,ws,4);delta=tuple(sub(a,b) for a,b in zip(wr,rr))
                    ct=schedule_constants(ws,n)
                    check(delta[0]==zeros(d) and delta[1]==zeros(d),'lower coefficients')
                    check(delta[2]==scale(v,ct['c']),'variance coefficient')
                    check(projected(delta[3],allrows,K)==projected(scale(mul(v,h),-ct['b']),allrows,K),'cubic kernel column')
                    hvh=mul(mul(h,v),h)
                    check(projected(delta[4],K,K)==projected(scale(hvh,ct['a']),K,K),'fourth kernel block')
                    check(ct['gamma']>0,'weighted Schur coefficient positivity')
                    fixtures+=1;coefficient_checks+=4
                    if mode=='unequal' and n<=4 and d==2:
                        dwr,drr=direct_expectations(hs,ws,4)
                        check(dwr==wr and drr==rr,'independent path enumeration')
                        direct+=1
                    if mode=='constant':
                        q=F(m*(m-1),n-1)
                        check(ct['c']==2*q,'closed c')
                        check(ct['b']==q*F(8*m-7,6),'closed b')
                        check(ct['a']==q*F((m-2)*(2*m-1),3),'closed a')
                        check(ct['gamma']==q*F((4*m+1)**2,72),'closed gamma')
                    # Weighted loss second-order formula.
                    g=matrix([[3 if i==j else (1 if abs(i-j)==1 else 0) for j in range(d)] for i in range(d)])
                    gw,gr=expectations(hs,ws,2,g)
                    W=mean(mul(mul(a,g),a) for a in ds)
                    J=add(W,scale(add(mul(v,g),mul(g,v)),F(1,2)))
                    check(sub(gw[2],gr[2])==scale(J,2*ct['e2']/F(n-1)),'weighted metric coefficient')
    # Exact matrix identity and rational gaps at 40 step sizes.
    H=matrix([[2,1],[1,2]]);D=matrix([[1,0],[0,0]])
    hs=(add(H,D),sub(H,D));ws=(F(1),F(1))
    wr,rr=expectations(hs,ws,4)
    for k in range(2,42):
        eta=F(1,2**k);x=(3*eta/4,F(1))
        diff=sub(evaluate(rr,eta),evaluate(wr,eta))
        check(quadratic(diff,x)==F(9,8)*eta**4*(2-9*eta**2),'exact distance gap')
        check(quadratic(diff,x)>0,'all stable test steps reverse')
    gw,gr=expectations(hs,ws,4,H)
    for k in range(4,25):
        eta=F(1,2**k);x=(F(-1,8),F(1))
        diff=sub(evaluate(gr,eta),evaluate(gw,eta))
        check(quadratic(diff,x)/2==eta**2*(120*eta**2-61*eta+4)/64,'objective gap')
        check(quadratic(diff,x)>0,'fixed-state loss reversal')
    # Diagnostic negative and positive branches; exact rational thresholds.
    objects=[
        ([[[3,1],[1,2]],[[1,1],[1,2]]],[1,1],'eventual_reversal'),
        ([[[3,0],[0,2]],[[1,0],[0,2]]],[1,1],'eventual_domination'),
        ([[[3,1],[1,3]],[[1,1],[1,1]]],[1,2],'eventual_domination'),
        ([[[2,1],[1,2]],[[2,1],[1,2]]],[1,1],'identical'),
    ]
    certificates=[]
    for data,weights,expected in objects:
        cert=classify(data,weights)
        check(cert['classification']==expected,'classifier branch')
        if expected=='eventual_reversal':
            hs2=tuple(matrix(a) for a in data);ws2=tuple(F(a) for a in weights)
            ww,rr2=expectations(hs2,ws2,2*len(weights))
            et=F(str(cert['step_threshold']))
            xx=cert['kernel_witness']+s.Rational(str(et))*cert['witness_linear_term']
            x=tuple(F(str(a)) for a in xx)
            val=quadratic(sub(evaluate(ww,et),evaluate(rr2,et)),x)
            target=-F(str(cert['constants']['gamma']))*F(str(cert['leakage_energy']))*et**4/2
            check(val<=target,'negative rational certificate bound')
        if expected=='eventual_domination':
            hs2=tuple(matrix(a) for a in data);ws2=tuple(F(a) for a in weights)
            ww,rr2=expectations(hs2,ws2,2*len(weights))
            et=F(str(cert['step_threshold']))
            lower=scale(matrix(cert['variance'].tolist()),F(str(cert['constants']['c']))*et**2/2)
            residual=sub(sub(evaluate(ww,et),evaluate(rr2,et)),lower)
            check(residual[0][0]>=0 and residual[1][1]>=0 and
                  residual[0][0]*residual[1][1]-residual[0][1]**2>=0,
                  'positive rational certificate bound')
        certificates.append(serialize(cert))
    # Rank-one components (with and without a common isotropic shift).
    rank_one_checks=0
    for n in range(2,6):
        for shift in (0,3):
            d=4
            vecs=[s.Matrix([rng.randrange(-2,3) for _ in range(d)]) for _ in range(n)]
            data=[(a*a.T+shift*s.eye(d)).tolist() for a in vecs]
            cert=classify(data,[1]*n)
            check(cert['classification'] in ('identical','eventual_domination'),
                  'rank-one/isotropic-shift corollary')
            rank_one_checks+=1
    # The finite degree-six schedule identity: fixed integer table, independently expanded.
    table={
      (4,2):4,(3,3):4,(2,4):1,
      (4,1,1):8,(3,2,1):20,(3,1,2):20,(2,3,1):8,(2,2,2):38,
      (2,1,3):12,(1,4,1):4,(1,3,2):18,(1,2,3):12,(1,1,4):2,
      (3,1,1,1):48,(2,2,1,1):64,(2,1,2,1):68,(2,1,1,2):72,
      (1,3,1,1):32,(1,2,2,1):64,(1,2,1,2):70,(1,1,3,1):24,
      (1,1,2,2):68,(1,1,1,3):24,
      (2,1,1,1,1):160,(1,2,1,1,1):144,(1,1,2,1,1):136,
      (1,1,1,2,1):136,(1,1,1,1,2):144,(1,1,1,1,1,1):320}
    from itertools import combinations
    a=s.symbols('a1:7');E={k:sum((s.prod(t) for t in combinations(a,k)),s.Integer(0)) for k in range(1,5)}
    w=[a[j]*sum(a[:j]) for j in range(6)]
    B=2*E[3]+2*E[1]*E[2]-sum(a[j]*w[j] for j in range(6))
    A=2*E[4]+2*E[1]*E[3]+E[2]**2-sum(t*t for t in w)
    poly=s.Poly(s.expand(B*B-4*E[2]*A),*a)
    independent=0
    for powers,c in poly.terms():
        pattern=tuple(k for k in powers if k)
        check(table.get(pattern)==c,'ordered monomial coefficient')
        independent+=1
    expansion=0
    for pattern,c in table.items():
        expansion+=c*sum((s.prod(a[i]**p for i,p in zip(idx,pattern))
                          for idx in combinations(range(6),len(pattern))),s.Integer(0))
    check(s.expand(poly.as_expr()-expansion)==0,'complete degree-six identity')
    # Exact symbolic two-component polynomial identities.
    eta=s.symbols('eta');HM=s.Matrix([[2,1],[1,2]]);DM=s.diag(1,0)
    P=s.eye(2)-eta*HM;Q=eta*DM
    identity=Q**2*P**2+Q*P*Q*P+P*Q*P*Q+P**2*Q**2
    target=s.Matrix([[2*eta**2*(9*eta**2-8*eta+2),3*eta**3*(2*eta-1)],
                     [3*eta**3*(2*eta-1),0]])
    check((identity-target).applyfunc(s.expand)==s.zeros(2),'symbolic two-matrix identity')
    output=dict(status='PASS',assertions=assertions,coefficient_fixtures=fixtures,
                coefficient_blocks_checked=coefficient_checks,direct_enumeration_fixtures=direct,
                ordered_monomial_patterns=len(table),six_variable_monomials=independent,rank_one_fixtures=rank_one_checks,
                python=platform.python_version(),sympy=s.__version__,elapsed_seconds=round(time.perf_counter()-start,3),
                qualification='Exact finite checks and a degree-six polynomial identity; not a proof-assistant formalization.')
    (ROOT/'results').mkdir(exist_ok=True)
    (ROOT/'results'/'verification.json').write_text(json.dumps(output,indent=2)+'\n')
    (ROOT/'certificates'/'diagnostic_examples.json').write_text(json.dumps(certificates,indent=2)+'\n')
    (ROOT/'certificates'/'schedule_identity.json').write_text(json.dumps([{ 'powers':list(k),'coefficient':v} for k,v in table.items()],indent=2)+'\n')
    print(json.dumps(output,indent=2))
if __name__=='__main__': main()
