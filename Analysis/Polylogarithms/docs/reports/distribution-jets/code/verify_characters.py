#!/usr/bin/env python3
"""Exact character phases, conductor counts, and determinant-factor checks.

Characters are represented by rational arguments modulo 1, not complex
floating-point numbers. SymPy is used only to find odd-prime-power primitive
roots. The underlying checks are finite exact arithmetic.
"""
from __future__ import annotations
from fractions import Fraction as F
from itertools import product
from collections import Counter
from pathlib import Path
import argparse,json
from sympy import primitive_root
from distribution import factor,divisors,units,phi,order


def characters(q):
    local=[]
    for p,e in factor(q).items():
        m=p**e
        if p != 2:
            generators=[(int(primitive_root(m)),phi(m))]
        elif e == 1:
            generators=[]
        elif e == 2:
            generators=[(m-1,2)]
        else:
            generators=[(m-1,2),(5,2**(e-2))]
        orders=[h for _,h in generators]
        logs={}
        for powers in product(*(range(h) for h in orders)):
            a=1
            for (g,h),k in zip(generators,powers):
                a=a*pow(g,k,m)%m
            logs[a]=powers
        assert len(logs)==phi(m)
        local.append((m,orders,logs))
    orders=[h for _,hs,_ in local for h in hs]
    us=units(q)
    for labels in product(*(range(h) for h in orders)):
        values={}
        for u in us:
            phase=F(0);offset=0
            for m,hs,logs in local:
                for k,h in zip(logs[u%m],hs):
                    phase+=F(labels[offset]*k,h);offset+=1
            values[u]=phase%1
        conductor=None
        for d in divisors(q):
            image={}
            for u,v in values.items():
                image.setdefault(u%d,set()).add(v)
            if all(len(v)==1 for v in image.values()):
                conductor=d;break
        assert conductor is not None
        def phase_at(n, f=conductor, vals=values):
            return next(v for u,v in vals.items() if u%f==n%f)
        phases={p:phase_at(p) for p in factor(q) if conductor%p != 0}
        yield dict(labels=labels, conductor=conductor, values=values,
                   unramified_phases=phases, rho=sum(v==0 for v in phases.values()))


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--max-q',type=int,default=60)
    args=ap.parse_args();records=[];examples={}
    if args.max_q < 2: ap.error('--max-q must be at least 2')
    for q in range(2,args.max_q+1):
        cs=list(characters(q));assert len(cs)==phi(q)
        assert sum(len(divisors(q//c['conductor']))-1 for c in cs)==q-phi(q)
        determinant=[]
        for p,e in factor(q).items():
            M=q//p**e;h=order(p,M)
            exponent=0;phases=[]
            for c in cs:
                f=c['conductor'];ef=factor(f).get(p,0)
                exponent+=e-max(1,ef)
                if ef==0:phases.append(c['unramified_phases'][p])
            assert exponent==phi(M)*(p**(e-1)-1)
            assert Counter(phases)==Counter({F(j,h):phi(M)//h for j in range(h)})
            determinant.append(dict(prime=p,power=e,complement=M,order=h,
                                    monomial_exponent=exponent,root_multiplicity=phi(M)//h))
        ranks=[sum(max(N+1-c['rho'],0) for c in cs) for N in range(4)]
        records.append(dict(q=q,phi=phi(q),rho_histogram=dict(Counter(c['rho'] for c in cs)),
                            primitive_jet_ranks=ranks))
        if q in (12,21,30):
            examples[str(q)]=dict(determinant_factors=determinant,
                characters=[dict(conductor=c['conductor'],labels=list(c['labels']),rho=c['rho'],
                    phases={str(p):str(v) for p,v in c['unramified_phases'].items()}) for c in cs],
                primitive_jet_ranks=ranks)
    for q,expected in [(12,[3,6,10]),(21,[10,21,33])]:
        if q <= args.max_q:
            assert next(x for x in records if x['q']==q)['primitive_jet_ranks'][:3]==expected
    root=Path(__file__).resolve().parents[1]
    (root/'data'/'character_checks.json').write_text(json.dumps(records,indent=2)+'\n')
    (root/'certificates'/'character_examples.json').write_text(json.dumps(examples,indent=2)+'\n')
    print(f'PASS: conductors, determinant root multiplicities and jet ranks for 2 <= q <= {args.max_q}.')

if __name__=='__main__':main()
