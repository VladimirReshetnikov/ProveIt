"""Reproduce exact-enumeration and interval-backend checks.
Run from the package root: python tests/run_checks.py
"""
from __future__ import annotations
import csv
import itertools
import json
import random
import sys
from fractions import Fraction as Q
from pathlib import Path
from time import perf_counter
import mpmath as mp

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'code'))
from fourier_tv import (ProductPair, MarkovPair, relative_certificate, relative_fast,
                         periodic_table, periodic_tv_certificate, bayes_risk_certificate)


def distribution(pair, first=True):
    if isinstance(pair,ProductPair):
        rows=pair.p if first else pair.q
        result=[]
        for xs in itertools.product(*(range(len(r)) for r in rows)):
            v=Q(1)
            for r,x in zip(rows,xs): v*=r[x]
            result.append(v)
        return result
    r=pair.p0 if first else pair.q0
    matrices=pair.p if first else pair.q
    result=[]
    for xs in itertools.product(range(len(r)),repeat=len(matrices)+1):
        v=r[xs[0]]
        for i,M in enumerate(matrices): v*=M[xs[i]][xs[i+1]]
        result.append(v)
    return result


def exact_tv(pair):
    p,q=distribution(pair),distribution(pair,False)
    return sum(abs(a-b) for a,b in zip(p,q))/2


def exact_risk(pair,alpha):
    return sum(min(alpha*a,(1-alpha)*b) for a,b in zip(distribution(pair),distribution(pair,False)))


def bernoulli(ps,qs):
    return ProductPair.create([[p,1-p] for p in ps],[[q,1-q] for q in qs])


def interval_case(name,pair,eps=Q(1,5)):
    t=perf_counter()
    cert=relative_certificate(pair,eps,dps=40)
    d=exact_tv(pair)
    assert cert.lower<=d<=cert.upper,(name,cert,d)
    assert abs(cert.estimate-d)<=eps*d,(name,'relative error')
    out=cert.as_dict()
    out.update(name=name,exact_tv=str(d),exact_tv_float=float(d),estimate_float=float(cert.estimate),
               lower_float=float(cert.lower),upper_float=float(cert.upper),seconds=perf_counter()-t,
               observed_relative_error=float(abs(cert.estimate-d)/d) if d else 0.0,
               support_size=len(distribution(pair)),input_size=pair.input_size)
    return out


def random_row(rng,q,allow_zero=False):
    raw=[rng.randint(0 if allow_zero else 1,20) for _ in range(q)]
    if not sum(raw): raw[0]=1
    return [Q(x,sum(raw)) for x in raw]


def alias_checks():
    mp.mp.dps=70
    rng=random.Random(8128)
    count=0
    max_error=mp.mpf(0)
    # Include partial common support and likelihoods far beyond the period.
    arrays=[([Q(1,2),Q(1,2)],[Q(1,2),Q(1,2)]),
            ([Q(0),Q(1,4),Q(3,4)],[Q(1,4),Q(0),Q(3,4)]),
            ([Q(1,10**30),1-Q(1,10**30)],[Q(3,4),Q(1,4)])]
    arrays += [(random_row(rng,4,True),random_row(rng,4,True)) for _ in range(25)]
    conv=lambda v: mp.mpf(v.numerator)/v.denominator
    for pp,qq in arrays:
        p,q=list(map(conv,pp)),list(map(conv,qq))
        d=sum(abs(a-b) for a,b in zip(p,q))/2
        common=[(a,b) for a,b in zip(p,q) if a*b>0]
        U=sum(a+b for a,b in common)
        O=sum(min(a,b) for a,b in common)
        A=sum(mp.sqrt(a*b) for a,b in common)
        m1=sum(mp.sqrt(a*b)*abs(mp.log(a/b)) for a,b in common)
        m2=sum(mp.sqrt(a*b)*mp.log(a/b)**2 for a,b in common)
        assert m1<=2*d+mp.mpf('1e-60')
        assert m2<=6*d+mp.mpf('1e-60')
        for L in [mp.mpf(1),mp.mpf(3),mp.mpf(8),mp.mpf(20)]:
            rho=mp.exp(-L/2)
            g0=(1+rho)/(1-rho)
            C=mp.mpf(0)
            R=mp.mpf(0)
            for a,b in common:
                s=mp.log(a/b)
                x=s-L*mp.floor(s/L)
                C+=mp.sqrt(a*b)*(mp.exp(-x/2)+mp.exp(-(L-x)/2))/(1-rho)
                for k in range(1,int(mp.floor(abs(s)/L))+1):
                    u=mp.exp(k*L)
                    R+=rho**k*(max(a-u*b,0)+max(b-u*a,0))
            B=U*rho/(1-rho)
            err=abs((B-(C-O))-R)
            max_error=max(max_error,err)
            assert err<mp.mpf('1e-55'),err
            assert C>=O-mp.mpf('1e-55') and C-O<=B+mp.mpf('1e-55')
            dc=U/2-O
            V=U*g0/2-C
            assert dc-mp.mpf('1e-55')<=V<=g0*dc+mp.mpf('1e-55')
            count+=1
    return dict(count=count,max_identity_residual=mp.nstr(max_error,8),precision_digits=70)


def main():
    (ROOT/'data').mkdir(exist_ok=True)
    rng=random.Random(20261008)
    cases=[
      ('equal_with_zeros',bernoulli([Q(0),Q(1,2)],[Q(0),Q(1,2)])),
      ('disjoint',bernoulli([Q(0),Q(1,3)],[Q(1),Q(1,3)])),
      ('one_coordinate',bernoulli([Q(1,2)],[Q(2,3)])),
      ('partial_support',bernoulli([Q(0),Q(1,2),Q(3,4)],[Q(1,3),Q(2,3),Q(1)])),
      ('heterogeneous_binary',bernoulli([Q(1,5),Q(2,3),Q(4,7),Q(1,10)],
                                      [Q(1,3),Q(1,2),Q(3,7),Q(1,7)])),
      ('rare_probability',bernoulli([Q(1,10**30),Q(1,2)],[Q(3,4),Q(2,3)])),
      ('tiny_distance_1e-12',bernoulli([Q(1,2)],[Q(1,2)+Q(1,10**12)])),
      ('near_equal_4d',bernoulli([Q(1,2)]*4,[Q(1,2)+Q(i,10**5) for i in range(1,5)])),
    ]
    cases.append(('tiny_distance_3d',bernoulli([Q(1,2)]*3,[Q(1,2)+Q(1,10**12)]*3)))
    cases.append(('fine_tolerance_1e-2',cases[4][1]))
    for i in range(8):
        qs=[2+rng.randrange(3) for _ in range(2+i%3)]
        p=[random_row(rng,q,True) for q in qs]
        q=[random_row(rng,q,True) for q in qs]
        cases.append((f'random_product_{i+1}',ProductPair.create(p,q)))
    M1=[[[Q(3,4),Q(1,4)],[Q(1,3),Q(2,3)]]]*3
    M2=[[[Q(2,3),Q(1,3)],[Q(1,4),Q(3,4)]]]*3
    cases.append(('markov_positive',MarkovPair.create([Q(1,2)]*2,[Q(1,3),Q(2,3)],M1,M2)))
    cases.append(('markov_with_zeros',MarkovPair.create([1,0],[Q(1,2)]*2,
                 [[[1,0],[Q(1,2)]*2],[[Q(1,2)]*2,[0,1]]],
                 [[[Q(1,2)]*2,[0,1]],[[1,0],[Q(1,3),Q(2,3)]]])))
    cases.append(('markov_unreachable_equality',MarkovPair.create([1,0],[1,0],
                 [[[1,0],[1,0]]],[[[1,0],[0,1]]])))
    for i in range(2):
        p0,q0=random_row(rng,3),random_row(rng,3)
        P=[[random_row(rng,3,True) for _ in range(3)] for _ in range(2)]
        Qm=[[random_row(rng,3,True) for _ in range(3)] for _ in range(2)]
        cases.append((f'random_markov_{i+1}',MarkovPair.create(p0,q0,P,Qm)))
    records=[]
    for name,pair in cases:
        rec=interval_case(name,pair,Q(1,100) if name=='fine_tolerance_1e-2' else Q(1,5))
        records.append(rec)
        print(name,rec['nodes'],f"{rec['seconds']:.3f}s",flush=True)
    # Exhaustive finite test: two Bernoulli coordinates, five choices each.
    grid=[Q(0),Q(1,4),Q(1,2),Q(3,4),Q(1)]
    laws=list(itertools.product(grid,repeat=2))
    max_rel=0.0
    checked=0
    for p in laws:
        for q in laws:
            pair=bernoulli(p,q)
            d=exact_tv(pair)
            result=relative_fast(pair,0.2)
            assert result['lower']-1e-12<=float(d)<=result['upper']+1e-12
            err=abs(result['estimate']-float(d))/float(d) if d else 0
            assert err<=0.2+1e-12
            max_rel=max(max_rel,err)
            checked+=1
    # Common periodic data: certify TV and 51 different Bayes priors.
    pair=cases[4][1]
    table=periodic_table(pair,Q(1,100),dps=40)
    additive=periodic_tv_certificate(table,Q(1,100))
    true=exact_tv(pair)
    assert additive.lower<=true<=additive.upper
    assert additive.upper-additive.lower<=Q(1,100)
    riskrows=[]
    for j in range(51):
        alpha=Q(j,50)
        lo,hi=bayes_risk_certificate(table,alpha)
        exact=exact_risk(pair,alpha)
        assert lo<=exact<=hi
        riskrows.append(dict(alpha=str(alpha),exact_risk=str(exact),lower=str(lo),upper=str(hi)))
    aliases=alias_checks()
    out=dict(interval_cases=records,exhaustive_fast_cases=checked,
             exhaustive_max_relative_error=max_rel,
             bayes_prior_checks=len(riskrows),periodic_tv=additive.as_dict(),
             alias_checks=aliases,all_checks_passed=True,
             interval_backend='mpmath.iv 1.3.0; exact rational endpoints',
             note='Fast checks are numerical cross-checks, not roundoff certificates or proofs.')
    (ROOT/'data'/'verification.json').write_text(json.dumps(out,indent=2))
    (ROOT/'data'/'bayes_risk_certificates.json').write_text(json.dumps(riskrows,indent=2))
    columns=['name','input_size','support_size','exact_tv_float','estimate_float','lower_float',
             'upper_float','nodes','decimal_precision','observed_relative_error','seconds']
    with (ROOT/'data'/'interval_cases.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=columns,extrasaction='ignore');w.writeheader();w.writerows(records)
    print('ALL CHECKS PASSED:',len(records),'interval cases,',checked,'fast cases,',len(riskrows),'priors,',aliases['count'],'alias identities.')

if __name__=='__main__':main()
