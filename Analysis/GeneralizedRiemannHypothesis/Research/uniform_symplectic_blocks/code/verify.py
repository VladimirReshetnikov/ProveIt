#!/usr/bin/env python3
"""Exact finite laws and reproducible numerical checks for symplectic blocks.

All finite probabilities use fractions.Fraction. Integer q may be any prime
power: these counting formulas do not implement finite-field arithmetic.
Independent exhaustive finite-field enumeration is in exhaustive_check.py.
The numerical checks illustrate the asymptotic theorem; they do not prove it.
Run from any directory: python3 verify.py [--quick]
"""
from __future__ import annotations
from fractions import Fraction as F
from functools import lru_cache
from decimal import Decimal, localcontext
from pathlib import Path
import argparse
import csv
import json
import time

ROOT = Path(__file__).resolve().parents[1]

@lru_cache(None)
def qbin(q: int, n: int, j: int) -> int:
    if j < 0 or j > n:
        return 0
    j = min(j, n-j)
    z = F(1)
    for i in range(j):
        z *= F(q**(n-i)-1, q**(j-i)-1)
    assert z.denominator == 1
    return z.numerator

@lru_cache(None)
def gl(q: int, n: int) -> int:
    z = 1
    for i in range(n):
        z *= q**n-q**i
    return z

@lru_cache(None)
def sp(q: int, dimension: int) -> int:
    assert dimension % 2 == 0
    h = dimension//2
    z = q**(h*h)
    for i in range(1, h+1):
        z *= q**(2*i)-1
    return z

@lru_cache(None)
def emb(q: int, dimension: int, j: int, s: int) -> int:
    """Isometric injections of a j-space of alternating rank 2s."""
    if s < 0 or 2*s > j or j-s > dimension//2:
        return 0
    z = sp(q, dimension)//sp(q, dimension-2*s)
    for i in range(j-2*s):
        z *= q**(dimension-2*s-i)-q**i
    return z

@lru_cache(None)
def subspace_type(q: int, dimension: int, j: int, s: int) -> int:
    aut = sp(q, 2*s)*gl(q, j-2*s)*q**(2*s*(j-2*s))
    value = emb(q, dimension, j, s)
    assert value % aut == 0
    return value//aut

@lru_cache(None)
def eta(q: int, h: int) -> F:
    z = F(1)
    for i in range(1,h+1):
        z *= 1-F(1,q**(2*i))
    return z

def invert_moments(q: int, moments: list[F]) -> list[F]:
    """Invert mu_j = sum_{k>=j} [k choose j]_q p_k exactly."""
    b = len(moments)-1
    p = [F(0)]*(b+1)
    for k in range(b,-1,-1):
        p[k] = moments[k]-sum((qbin(q,j,k)*p[j] for j in range(k+1,b+1)),F(0))
    assert sum(p) == 1
    assert min(p) >= 0
    return p

def finite_laws(q: int, a: int, b: int) -> dict:
    assert q >= 2 and a >= b >= 2 and a % 2 == b % 2 == 0
    ma, mu, md, mt = [],[],[],[]
    for j in range(b+1):
        ntypes = [(s,subspace_type(q,b,j,s)) for s in range(j//2+1)]
        assert sum(n for s,n in ntypes) == qbin(q,b,j)
        ma.append(sum((F(n*emb(q,b,j,s),emb(q,a+b,j,s))
                       for s,n in ntypes if n),F(0)))
        mu.append(F(qbin(q,b,j),q**(a*j)))
        md.append(sum((F(n*emb(q,a,j,s)*q**((a-j)*(b-j)),q**(a*b))
                       for s,n in ntypes if n),F(0)))
        mt.append(F(qbin(q,b,j),q**(b*j-j*(j+1)//2)))
    pa, pu, pd, pt = [invert_moments(q,m) for m in (ma,mu,md,mt)]
    assert all(pd[k] == pt[k] == 0 for k in range(1,b+1,2))
    # A separate kernel-count formula for the iid rectangular probabilities.
    for k in range(b+1):
        count = qbin(q,b,k)
        for i in range(b-k):
            count *= q**a-q**i
        assert pu[k] == F(count,q**(a*b))
    alpha = eta(q,a//2)*eta(q,b//2)/eta(q,(a+b)//2)
    rank_tv = sum(abs(x-y) for x,y in zip(pa,pu))/2
    defect_tv = sum(abs(x-y) for x,y in zip(pd,pt))/2
    full_tv = (1-alpha)*pd[0]
    # Independently reconstruct the residual likelihood distribution.
    tilted = []
    for k in range(b//2+1):
        weight = sum((F(qbin(q,2*k,r),q**(r*(r+1)//2))/eta(q,r-k)
                      for r in range(k,2*k+1)),F(0))
        likelihood = alpha*weight
        assert (likelihood < 1) if k == 0 else (likelihood > 1)
        tilted.append(pd[2*k]*likelihood)
    assert sum(tilted) == 1
    assert sum(abs(tilted[k]-pd[2*k]) for k in range(b//2+1))/2 == full_tv
    return dict(q=q,a=a,b=b,rank_A=pa,rank_U=pu,defect_U=pd,alternating=pt,
                alpha=alpha,rank_tv=rank_tv,defect_tv=defect_tv,full_tv=full_tv)

def dec(x) -> Decimal:
    if isinstance(x,F):
        return Decimal(x.numerator)/Decimal(x.denominator)
    return Decimal(x)

def asymptotics(laws: dict) -> dict:
    q,a,b = (laws[k] for k in ('q','a','b'))
    d = a-b
    with localcontext() as ctx:
        ctx.prec = 100
        Q = Decimal(q)
        cutoff = max(180,a+b+40)
        gamma = [Decimal(1)]
        eta_inf,theta_inf = Decimal(1),Decimal(1)
        for j in range(1,cutoff+1):
            gamma.append(gamma[-1]*(1-Q**(-j)))
            eta_inf *= 1-Q**(-2*j)
            theta_inf *= 1-Q**(-(2*j-1))
        gamma_inf = gamma[-1]
        delta = theta_inf*(1-eta_inf)
        cq = theta_inf*(Q-(Q+1)*eta_inf)/(Q*Q-1)
        rank_lead = Q**(-a)*gamma_inf/((Q-1)*gamma[d])
        defect_lead = Q**(-a)*Q*theta_inf/(Q*Q-1)
        full_lead = delta+cq*(Q**(-a)+Q**(-b))
        rank_l1 = Decimal(0)
        defect_l1 = Decimal(0)
        for k in range(max(b+16,48)):
            pi = gamma_inf*Q**(-k*(k+d))/(gamma[k]*gamma[k+d])
            chi = (Q**d+1-Q**(d+k))*pi/(Q-1)
            actual = dec(laws['rank_A'][k]-laws['rank_U'][k]) if k<=b else Decimal(0)
            rank_l1 += abs(actual-Q**(-a)*chi)
            if k%2==0:
                lam = theta_inf*Q**(-(k//2)*(k-1))/gamma[k]
                zeta = (Q+1-Q**k)*lam/(Q*Q-1)
                actd = dec(laws['defect_U'][k]-laws['alternating'][k]) if k<=b else Decimal(0)
                defect_l1 += abs(actd-Q**(-a)*zeta)
        return {"delta":str(delta),"c_q":str(cq),
                "rank_tv_leading":str(rank_lead),"rank_tv_ratio":str(dec(laws['rank_tv'])/rank_lead),
                "defect_tv_leading":str(defect_lead),"defect_tv_ratio":str(dec(laws['defect_tv'])/defect_lead),
                "full_tv_first_order":str(full_lead),
                "rank_l1_scaled":str(rank_l1*Q**(a+b)),
                "defect_l1_scaled":str(defect_l1*Q**(a+b)),
                "full_error_scaled":str(abs(dec(laws['full_tv'])-full_lead)/(Q**(-a)+Q**(-b))**2)}

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--quick',action='store_true')
    args=parser.parse_args()
    start=time.monotonic()
    out=ROOT/'results'
    out.mkdir(parents=True,exist_ok=True)
    cases=set()
    for q in (2,3,4,5):
        for b in range(2, (10 if args.quick else 26),2):
            for a in (b,b+2,2*b):
                cases.add((q,a,b))
    if not args.quick:
        cases.update((2,b+2,b) for b in (28,32,40,48))
        cases.update((2,2*b,b) for b in (28,32))
    rows=[]
    for q,a,b in sorted(cases):
        x=finite_laws(q,a,b)
        r={k:x[k] for k in ('q','a','b')}
        for k in ('rank_tv','full_tv','defect_tv'):
            r[k+'_exact']=str(x[k]);r[k]=str(dec(x[k]))
        r.update(asymptotics(x))
        rows.append(r)
    with (out/'exact_distances.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
    summary={"cases":len(rows),"q_values":[2,3,4,5],
      "checks":["Nonnegative normalized exact rank and residual distributions",
                "All odd residual nullities have exactly zero mass",
                "Subspace type counts sum to the Gaussian binomial coefficient",
                "Iid rank law agrees with independent kernel-count formula",
                "Residual likelihood normalizes exactly and has the claimed sign",
                "Optimal residual event gives exactly the full total variation"],
      "max_scaled_rank_l1_observed":str(max(Decimal(r['rank_l1_scaled']) for r in rows)),
      "max_scaled_defect_l1_observed":str(max(Decimal(r['defect_l1_scaled']) for r in rows)),
      "max_scaled_full_error_observed":str(max(Decimal(r['full_error_scaled']) for r in rows)),
      "status":"PASS", "seconds":round(time.monotonic()-start,3),
      "interpretation":"Finite exact checks and numerical illustration; proof is in the paper."}
    (out/'verification.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))

if __name__=='__main__':
    main()
