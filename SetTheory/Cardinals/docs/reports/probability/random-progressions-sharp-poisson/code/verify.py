#!/usr/bin/env python3
"""Exact finite regressions for sharp AP avoidance asymptotics.

These checks are NOT a formal proof of any asymptotic theorem.  All event,
mean, covariance and geometric identities below use integers/Fraction.
The entropy-profile table and logarithmic avoidance checks use floats.
Python 3.10+; standard library only.  Run from any directory.
"""
from __future__ import annotations
import argparse
import csv
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import combinations
import json
import math
from pathlib import Path
import time

ROOT = Path(__file__).resolve().parents[1]

@dataclass(frozen=True)
class Head:
    a: int
    d: int
    pos: int
    neg: int

    @property
    def support(self) -> int:
        return self.pos | self.neg

    def occurs(self, state: int) -> bool:
        return state & self.pos == self.pos and not state & self.neg


def heads(n: int, r: int) -> list[Head]:
    if n < 1 or r < 2:
        raise ValueError("Require n >= 1 and r >= 2")
    return [Head(a, d, sum(1 << (a + j*d - 1) for j in range(r)),
                 (1 << (a-d-1)) if a > d else 0)
            for d in range(1, (n-1)//(r-1)+1)
            for a in range(1, n-(r-1)*d+1)]


def count_ap(n: int, r: int) -> int:
    if n < 1 or r < 2:
        raise ValueError("Require n >= 1 and r >= 2")
    t = (n-1)//(r-1)
    return t*n - (r-1)*t*(t+1)//2


def joint(events: tuple[Head, ...], p: F) -> F:
    pos = neg = 0
    for e in events:
        pos |= e.pos
        neg |= e.neg
    if pos & neg:
        return F(0)
    return p ** pos.bit_count() * (1-p) ** neg.bit_count()


def influence(e: Head, x: int, p: F) -> F:
    bit = 1 << (x-1)
    if e.pos & bit:
        return joint((e,), p)/p
    if e.neg & bit:
        return -joint((e,), p)/(1-p)
    return F(0)


def exhaustive(n: int, r: int) -> dict:
    es = heads(n,r)
    # Counts indexed by number of selected coordinates.  No floating arithmetic.
    zero = [0]*(n+1)
    sums = [0]*(n+1)
    squares = [0]*(n+1)
    for state in range(1 << n):
        y = sum(e.occurs(state) for e in es)
        raw = any(state & e.pos == e.pos for e in es)
        assert (y == 0) == (not raw)
        k = state.bit_count()
        zero[k] += (y == 0)
        sums[k] += y
        squares[k] += y*y
    for p in (F(1,2), F(1,3)):
        weights = [p**k * (1-p)**(n-k) for k in range(n+1)]
        mean = sum((sums[k]*weights[k] for k in range(n+1)), F(0))
        expected = count_ap(n,r)*p**r-count_ap(n,r+1)*p**(r+1)
        assert mean == expected
        if n <= 10:
            second = sum((squares[k]*weights[k] for k in range(n+1)),F(0))
            pair_second = expected+2*sum((joint((a,b),p) for a,b in combinations(es,2)),F(0))
            assert second == pair_second
    return dict(n=n, r=r, configurations=1 << n,
                zero_by_cardinality=zero, first_moment_by_cardinality=sums,
                second_moment_by_cardinality=squares)


def pair_checks(n: int, r: int, p: F) -> dict:
    es = heads(n,r)
    pis = [joint((e,),p) for e in es]
    one = multi = incompatible_equal = 0
    s = [sum((influence(e,x,p) for e in es),F(0)) for x in range(1,n+1)]
    for x in range(1,n+1):
        bit = 1 << (x-1)
        deg = sum(bool(e.pos & bit) for e in es)
        boundary = sum(bool(e.pos & bit) and not e.neg for e in es)
        pred = sum(bool(e.neg & bit) for e in es)
        assert pred == (n-x)//r
        assert boundary <= (n-1)//(r-1)
        assert s[x-1] == (1-p)*p**(r-1)*deg+p**r*(boundary-pred)
    cov_one = F(0)
    cov_multi = F(0)
    projected_multi = F(0)
    for i,j in combinations(range(len(es)),2):
        a,b = es[i],es[j]
        overlap = a.support & b.support
        size = overlap.bit_count()
        z = joint((a,b),p)
        cov = z-pis[i]*pis[j]
        if not size:
            assert cov == 0
        if size == 1:
            one += 1
            x = overlap.bit_length()
            assert cov == p*(1-p)*influence(a,x,p)*influence(b,x,p)
            cov_one += cov
        elif size >= 2:
            multi += 1
            cov_multi += cov
            projected_multi += p*(1-p)*sum((influence(a,x,p)*influence(b,x,p)
                                      for x in range(1,n+1)),F(0))
        if size and a.d == b.d:
            assert z == 0
            incompatible_equal += 1
        if size and a.d != b.d:
            g = math.gcd(a.d,b.d)
            m = max(a.d//g,b.d//g)
            assert m*(size-1) <= r
    diag_projection = p*(1-p)*sum((influence(e,x,p)**2 for e in es
                                                for x in range(1,n+1)),F(0))/2
    norm = p*(1-p)*sum((v*v for v in s),F(0))/2
    assert cov_one == norm-diag_projection-projected_multi
    kappa2half = cov_one+cov_multi-sum((v*v for v in pis),F(0))/2
    return dict(n=n,r=r,p=str(p),events=len(es),one_overlap_pairs=one,
                multi_overlap_pairs=multi,equal_step_exclusions=incompatible_equal,
                second_factorial_cumulant_half=str(kappa2half))


def triple_checks(n: int, r: int) -> dict:
    es = heads(n,r)
    cases = [0,0,0]
    checked = connected = compatible = 0
    for a,b,c in combinations(es,3):
        checked += 1
        sizes = [(a.support & b.support).bit_count(),
                 (a.support & c.support).bit_count(),
                 (b.support & c.support).bit_count()]
        if sum(t>0 for t in sizes) < 2:
            continue
        connected += 1
        pos = a.pos | b.pos | c.pos
        neg = a.neg | b.neg | c.neg
        if pos & neg:
            continue
        compatible += 1
        multiple = sum(t>=2 for t in sizes)
        cls = min(2,multiple)
        cases[cls] += 1
        u = pos.bit_count()
        if cls == 0:
            assert u >= 3*r-3
        elif cls == 1:
            assert 2*u >= 5*r-6
        else:
            assert 3*u >= 5*r-9
    return dict(n=n,r=r,events=len(es),triples=checked,connected=connected,
                compatible=compatible,compatible_classes=cases)


def local_lemma_checks(rows: list[dict]) -> list[dict]:
    out = []
    for row in rows:
        n,r = row['n'],row['r']
        if n != 12 or r < 5:
            continue
        es = heads(n,r)
        for p in (F(1,4),F(1,3)):
            pis = [joint((e,),p) for e in es]
            b1=b2=F(0)
            delta=F(0)
            for i,a in enumerate(es):
                mass=sum((pis[j] for j,b in enumerate(es) if a.support & b.support),F(0))
                delta=max(delta,mass)
                b1+=pis[i]*mass
                b2+=sum((joint((a,b),p) for j,b in enumerate(es)
                          if i!=j and a.support & b.support),F(0))
            if delta>F(1,8):
                continue
            lam=sum(pis,F(0))
            p0=sum((v*p**k*(1-p)**(n-k) for k,v in enumerate(row['zero_by_cardinality'])),F(0))
            logp=math.log(float(p0))
            lo=float(-lam-4*b1)
            hi=float(-lam+2*b2)
            assert lo-1e-14 <= logp <= hi+1e-14
            out.append(dict(n=n,r=r,p=str(p),delta=str(delta),
                           log_avoidance=logp,lower=lo,upper=hi))
    return out


def degrees(n: int, r: int) -> list[int]:
    m=r-1
    ans=[0]*n
    for x in range(1,n+1):
        v=(n-x)//m+(x-1)//m
        for j in range(1,m):
            v+=min((x-1)//j,(n-x)//(m-j))
        ans[x-1]=v
    assert sum(ans)==r*count_ap(n,r)
    return ans


def profile(n: int, p: float=0.5) -> dict:
    r=2
    while count_ap(n,r)*p**r-count_ap(n,r+1)*p**(r+1)>1:
        r+=1
    ds=degrees(n,r)
    h=5/6-math.pi**2/18
    moment=sum(v*v for v in ds)/n**3
    return dict(n=n,r=r,p=p,lambda_exact=count_ap(n,r)*p**r-count_ap(n,r+1)*p**(r+1),
                normalized_degree_square=moment,H=h,error=moment-h,
                r_scaled_error=r*(moment-h))


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--quick',action='store_true',help='Smaller finite test set')
    parser.add_argument('--output',type=Path,default=ROOT/'results')
    args=parser.parse_args()
    started=time.time()
    args.output.mkdir(parents=True,exist_ok=True)
    maxn=10 if args.quick else 13
    exhaustive_rows=[exhaustive(n,r) for n in range(3,maxn+1)
                     for r in range(2,min(n,8)+1)]
    pair_rows=[pair_checks(n,r,p) for n in ((8,12) if args.quick else (8,12,18,24))
               for r in (3,4,6) if r<=n for p in (F(1,2),F(1,3),F(2,3))]
    triple_rows=[triple_checks(n,r) for n in ((12,) if args.quick else (18,24,30))
                 for r in (4,5,6,8) if r<=n]
    ll_rows=local_lemma_checks(exhaustive_rows)
    profiles=[profile(n) for n in ((100,1000) if args.quick else (100,1000,10000,100000))]
    with (args.output/'degree_profile.csv').open('w',newline='') as fh:
        wr=csv.DictWriter(fh,fieldnames=list(profiles[0]))
        wr.writeheader();wr.writerows(profiles)
    report=dict(status='PASS',formal_proof=False,
                arithmetic='Exact integers and fractions except labelled numerical diagnostics',
                elapsed_seconds=round(time.time()-started,3),
                configurations=sum(x['configurations'] for x in exhaustive_rows),
                exhaustive_parameter_cases=len(exhaustive_rows),
                pair_parameter_cases=len(pair_rows),
                one_overlap_covariance_checks=sum(x['one_overlap_pairs'] for x in pair_rows),
                multi_overlap_pair_checks=sum(x['multi_overlap_pairs'] for x in pair_rows),
                triple_geometry_checks=sum(x['triples'] for x in triple_rows),
                connected_compatible_triples=sum(x['compatible'] for x in triple_rows),
                local_avoidance_checks=len(ll_rows),
                exhaustive=exhaustive_rows,pairs=pair_rows,triples=triple_rows,
                local_avoidance=ll_rows,profiles=profiles)
    (args.output/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in
                     ('exhaustive','pairs','triples','local_avoidance','profiles')},indent=2))
    print('Results:',args.output)

if __name__=='__main__':
    main()
