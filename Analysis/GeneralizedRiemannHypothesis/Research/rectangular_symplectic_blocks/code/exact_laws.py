#!/usr/bin/env python3
"""Exact finite-field laws for complementary nondegenerate symplectic blocks.

All probability calculations use fractions.Fraction. No Monte Carlo samples.
Run from any directory; outputs are written next to this file in ../results.
The formulas are proved in paper.tex. This code verifies finite instances,
not the asymptotic theorem itself.
"""
from __future__ import annotations

from fractions import Fraction as F
from functools import lru_cache
from math import prod
from pathlib import Path
from decimal import Decimal, localcontext
import argparse
import csv
import json
import sys

# These are internally generated exact certificates, not external integer inputs.
if hasattr(sys, 'set_int_max_str_digits'):
    sys.set_int_max_str_digits(100000)


@lru_cache(None)
def qbin(q: int, n: int, k: int) -> int:
    if k < 0 or k > n:
        return 0
    k = min(k, n-k)
    num = prod(q**(n-i)-1 for i in range(k))
    den = prod(q**(k-i)-1 for i in range(k))
    assert num % den == 0
    return num//den


@lru_cache(None)
def gamma(q: int, n: int) -> F:
    return prod((F(q**i-1, q**i) for i in range(1,n+1)), start=F(1))


@lru_cache(None)
def eta(q: int, n: int) -> F:
    return prod((F(q**(2*i)-1,q**(2*i)) for i in range(1,n+1)), start=F(1))


@lru_cache(None)
def theta(q: int, n: int) -> F:
    return prod((F(q**(2*i-1)-1,q**(2*i-1)) for i in range(1,n+1)), start=F(1))


@lru_cache(None)
def gl_order(q: int, n: int) -> int:
    return prod(q**n-q**i for i in range(n))


@lru_cache(None)
def sp_order(q: int, n: int) -> int:
    assert n % 2 == 0
    return q**((n//2)**2)*prod(q**(2*i)-1 for i in range(1,n//2+1))


@lru_cache(None)
def emb(q: int, D: int, j: int, s: int) -> int:
    """Isometric injections of a j-dimensional form of rank 2s into dimension D."""
    assert D % 2 == 0
    if s < 0 or 2*s > j or j-s > D//2:
        return 0
    # Choose symplectic pairs, then an independent isotropic radical frame.
    pairs = prod((q**(D-2*i)-1)*q**(D-2*i-1) for i in range(s))
    radical = prod(q**(D-2*s-i)-q**i for i in range(j-2*s))
    return pairs*radical


@lru_cache(None)
def subspace_type(q: int, D: int, j: int, s: int) -> int:
    r = j-2*s
    if r < 0:
        return 0
    aut = sp_order(q,2*s)*gl_order(q,r)*q**(2*s*r)
    assert emb(q,D,j,s) % aut == 0
    return emb(q,D,j,s)//aut


def invert_moments(q: int, moments: list[F]) -> list[F]:
    """Triangular inversion of E[{K choose j}_q]."""
    b = len(moments)-1
    law = [F(0)]*(b+1)
    for j in range(b,-1,-1):
        law[j] = moments[j]-sum((qbin(q,k,j)*law[k] for k in range(j+1,b+1)), F(0))
    assert all(x >= 0 for x in law), law
    assert sum(law) == 1, sum(law)
    return law


def tv(p: list[F], q: list[F]) -> F:
    assert len(p) == len(q)
    return sum((abs(x-y) for x,y in zip(p,q)), F(0))/2


def defect_fullrank_positive_sum(q: int, a: int, b: int) -> F:
    """Positive-sum specialization of De Boeck--Van de Voorde, Theorem 4.9."""
    h=b//2
    return sum((theta(q,h-m)*F(qbin(q*q,h,m), q**(2*m*(h-m)+(a+1)*m))
                for m in range(h+1)), F(0))


def laws(q: int, a: int, b: int) -> dict:
    assert q >= 2 and a >= b >= 2 and a % 2 == b % 2 == 0
    mus=[]; mus0=[]; nus=[]; nus0=[]
    for j in range(b+1):
        assert sum(subspace_type(q,b,j,s) for s in range(j//2+1)) == qbin(q,b,j)
        mu=F(0); nu=F(0)
        for s in range(j//2+1):
            n=subspace_type(q,b,j,s)
            if not n:
                continue
            mu += F(n*emb(q,b,j,s), emb(q,a+b,j,s))
            nu += F(n*emb(q,a,j,s), q**((a+b)*j-j*j))
        mus.append(mu)
        mus0.append(F(qbin(q,b,j), q**(a*j)))
        nus.append(nu)
        nus0.append(F(qbin(q,b,j), q**(b*j-j*(j+1)//2)))
    rank=invert_moments(q,mus)
    rank0=invert_moments(q,mus0)
    defect=invert_moments(q,nus)
    alt=invert_moments(q,nus0)
    assert all(defect[k] == alt[k] == 0 for k in range(1,b+1,2))
    alpha=eta(q,a//2)*eta(q,b//2)/eta(q,(a+b)//2)
    full=(1-alpha)*defect[0]
    assert defect[0] == defect_fullrank_positive_sum(q,a,b)
    tilted=[]
    for k in range(b+1):
        if k % 2:
            tilted.append(F(0)); continue
        ell=k//2
        fibre=sum((F(qbin(q,2*ell,t),q**(t*(t+1)//2))/eta(q,t-ell)
                   for t in range(ell,2*ell+1)), F(0))
        likelihood=alpha*fibre
        assert (likelihood < 1) if k == 0 else (likelihood > 1)
        tilted.append(defect[k]*likelihood)
    assert sum(tilted) == 1
    assert tv(tilted,defect) == full
    return dict(q=q,a=a,b=b,alpha=alpha,rank=rank,rank_iid=rank0,
                defect=defect,defect_iid_alt=alt,defect_symplectic=tilted,
                full_tv=full,rank_tv=tv(rank,rank0),defect_tv=tv(defect,alt),
                rank_full_event_gap=rank[0]-rank0[0])


def dec(x: F, places: int=28) -> str:
    with localcontext() as ctx:
        ctx.prec=places
        return str(Decimal(x.numerator)/Decimal(x.denominator))


def exact_string(x):
    if isinstance(x,F): return str(x)
    if isinstance(x,dict): return {k:exact_string(v) for k,v in x.items()}
    if isinstance(x,list): return [exact_string(v) for v in x]
    return x


def product_enclosures(q: int, L: int=64) -> dict:
    """Rational certificates; prod(1-t_i) lies in [1-sum(t_i),1]."""
    e=eta(q,L); t=theta(q,L); g=gamma(q,2*L)
    elo=e*(1-F(1,q**(2*L)*(q*q-1)))
    tlo=t*(1-F(q,q**(2*L)*(q*q-1)))
    glo=g*(1-F(1,q**(2*L)*(q-1)))
    dlo=tlo*(1-e); dhi=t*(1-elo)
    return dict(q=q,factors=L,eta=[elo,e],theta=[tlo,t],gamma=[glo,g],Delta=[dlo,dhi])


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--quick', action='store_true', help='Only six direct-enumeration cases.')
    args=parser.parse_args()
    out=Path(__file__).resolve().parents[1]/'results'; out.mkdir(exist_ok=True)
    cases=[(2,2,2),(2,4,2),(2,4,4),(2,6,2),(3,2,2),(3,4,2)]
    if not args.quick:
        cases += [(q,b+d,b) for q in (2,3,4,5) for b in (2,4,6,8,12,16,24) for d in (0,2,6,16)]
        cases += [(2,26,24),(2,64,32),(2,40,38),(2,64,64)]
    cases=list(dict.fromkeys(cases))
    records=[]
    detailed=[]
    for q,a,b in cases:
        r=laws(q,a,b)
        g=gamma(q,160); e=eta(q,80); t=theta(q,80)
        coeff_rank=g/F(q-1)/gamma(q,a-b)
        rank_lead=coeff_rank/F(q**a)
        delta=t*(1-e)
        coeff_full=t*(q-(q+1)*e)/F(q*q-1)
        full_lead=delta+coeff_full*(F(1,q**a)+F(1,q**b))
        defect_lead=F(q)*t/F(q*q-1)/F(q**a)
        records.append(dict(q=q,a=a,b=b,full_tv=dec(r['full_tv']),
            rank_tv=dec(r['rank_tv']),rank_leading=dec(rank_lead),
            rank_ratio=dec(r['rank_tv']/rank_lead),
            defect_tv=dec(r['defect_tv']),defect_leading=dec(defect_lead),
            full_first_correction=dec(full_lead),
            scaled_rank_error=dec((r['rank_tv']-rank_lead)*q**(a+b)),
            scaled_defect_error=dec((r['defect_tv']-defect_lead)*q**(a+b)),
            scaled_full_error=dec((r['full_tv']-full_lead)*q**(2*b))))
        if (q,a,b) in cases[:6] or (q,a,b) in [(2,26,24),(2,64,32),(2,40,38)]:
            detailed.append(exact_string(r))
    with (out/'exact_table.csv').open('w',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=list(records[0])); writer.writeheader();writer.writerows(records)
    (out/'exact_laws.json').write_text(json.dumps(detailed,indent=2)+'\n')
    cert=[product_enclosures(q) for q in (2,3,4,5)]
    (out/'constant_enclosures.json').write_text(json.dumps(exact_string(cert),indent=2)+'\n')
    summary={'cases':len(cases),'checks':['nonnegative probabilities','normalization',
        'alternating parity','subspace type sum','positive-sum comparison',
        'likelihood normalization','likelihood sign','full TV from optimal event'],
        'status':'PASS','arithmetic':'exact rational','sampling':'none'}
    (out/'verification_summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary))
    for row in records:
        if (row['q'],row['a'],row['b']) in [(2,26,24),(2,64,32),(2,40,38)]:print(json.dumps(row))


if __name__=='__main__':
    main()
