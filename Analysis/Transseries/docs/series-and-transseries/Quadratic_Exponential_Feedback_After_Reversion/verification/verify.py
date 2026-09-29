#!/usr/bin/env python3
"""Exact EGF-normalized checks for quadratic exponential-feedback reversion.

Exact routines use the Python 3.10+ standard library. The command-line
audit additionally requires mpmath for non-rigorous decimal diagnostics.
The exact routines operate on c[n] = n! [z**n] V(z).
No numerical experiment is used as a proof of an asymptotic theorem.
"""
from __future__ import annotations
import argparse
import csv
import json
import math
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from time import perf_counter

@dataclass(frozen=True)
class Model:
    a: int = 1
    slopes: tuple[tuple[int, int], ...] = ()
    weights: tuple[tuple[int, int], ...] = ()
    def lam(self, j: int) -> int:
        return dict(self.slopes).get(j, self.a * j * j)
    def weight(self, j: int) -> int:
        return dict(self.weights).get(j, 1)
    def validate(self) -> None:
        if self.a <= 0 or self.weight(1) != 1:
            raise ValueError('a must be positive and w_1 must equal 1')
        if any(j < 1 or x < 0 for j,x in self.slopes + self.weights):
            raise ValueError('Overrides must have positive indices and nonnegative values')


def inverse_egf(N: int, model: Model, cutoff: int | None = None):
    """Compute inverse, or its constant/linear action-marker coefficients.

    cutoff=None gives V. Otherwise every primitive action j>cutoff has
    weight multiplied by s; return [s^0]V and [s^1]V=-T_cutoff.
    All entries are exact integers in exponential generating normalization.
    """
    model.validate()
    if N < 1 or (cutoff is not None and cutoff < 1):
        raise ValueError('N and cutoff must be positive')
    dual = cutoff is not None
    choose = [[math.comb(n,k) for k in range(n+1)] for n in range(N+1)]
    c = [0]*(N+1); c[1] = 1
    h = [0]*(N+1)
    # P[j][n] = n! [z^n] Q(z)^j; L is its first marker derivative.
    P = [[0]*(N+1) for _ in range(N+1)]
    L = [[0]*(N+1) for _ in range(N+1)] if dual else None
    P[0][0] = 1; P[1][1] = 1
    d = [0]*(N+1)
    powers = [None]*(N+1)
    for j in range(2,N+1):
        d[j] = model.lam(j)-model.lam(1)
        pp = [1]
        for k in range(N-j): pp.append(pp[-1]*d[j])
        powers[j] = pp
    b = model.lam(1)
    for n in range(2,N+1):
        cn = choose[n]
        for j in range(2,n+1):
            pm = P[j-1]
            total = 0; total_h = 0
            if dual:
                lm = L[j-1]
                for i in range(1,n-j+2):
                    cc=cn[i]
                    total += cc*c[i]*pm[n-i]
                    total_h += cc*(h[i]*pm[n-i]+c[i]*lm[n-i])
                L[j][n]=total_h
            else:
                for i in range(1,n-j+2):
                    total += cn[i]*c[i]*pm[n-i]
            P[j][n]=total
        val = n*((-b)**(n-1)); val_h=0
        for j in range(2,n+1):
            weight=model.weight(j)
            if not weight: continue
            pp=powers[j]; pj=P[j]
            s0=sum(cn[m]*pj[m]*pp[n-m] for m in range(j,n+1))
            if dual and j>cutoff:
                val_h -= weight*s0
            else:
                val -= weight*s0
                if dual:
                    lj=L[j]
                    s1=sum(cn[m]*lj[m]*pp[n-m] for m in range(j,n+1))
                    val_h -= weight*s1
        c[n]=val; P[1][n]=val
        if dual:
            h[n]=val_h; L[1][n]=val_h
    return (c,h) if dual else c


def partitions(n: int, largest: int | None = None):
    """Yield ordinary integer partitions as nonincreasing tuples."""
    if n == 0:
        yield ()
        return
    top=n if largest is None else min(n,largest)
    for k in range(top,0,-1):
        for rest in partitions(n-k,k): yield (k,)+rest


def partition_inverse(n: int, model: Model, cutoff: int | None=None):
    """Independent finite Lagrange/multiplicity formula, exact Fractions."""
    b=model.lam(1)
    zero=Fraction((-b)**(n-1), math.factorial(n-1))
    first=Fraction(0)
    whole=zero
    for K in range(1,n):
        for parts in partitions(K):
            counts={k:parts.count(k) for k in set(parts)}
            s=len(parts)
            weight=math.prod(model.weight(k+1)**m for k,m in counts.items())
            if not weight: continue
            A=sum(model.lam(k+1)*m for k,m in counts.items()) - b*(K+s+1)
            C=Fraction(math.factorial(K+s),math.factorial(K+1)*math.prod(math.factorial(m) for m in counts.values()))
            term=((-1)**s)*C*weight*Fraction(A**(n-K-1),math.factorial(n-K-1))
            whole+=term
            if cutoff is not None:
                marked=sum(m for k,m in counts.items() if k+1>cutoff)
                if marked==0: zero+=term
                elif marked==1: first+=term
    fac=math.factorial(n)
    return (zero*fac,first*fac) if cutoff is not None else whole*fac


def formal_composition_check(c: list[int], model: Model, N: int) -> list[Fraction]:
    """Check sum_j w_j V(z)^j exp(lambda_j*z) = z independently."""
    q=[Fraction(c[n],math.factorial(n)) for n in range(N+1)]
    powq=[Fraction(0)]*(N+1); powq[0]=1
    out=[Fraction(0)]*(N+1)
    for j in range(1,N+1):
        powq=[sum((powq[i]*q[n-i] for i in range(n+1)),Fraction(0)) for n in range(N+1)]
        lam=model.lam(j); w=model.weight(j)
        for n in range(j,N+1):
            out[n]+=w*sum((powq[m]*Fraction(lam**(n-m),math.factorial(n-m)) for m in range(j,n+1)),Fraction(0))
    return out


def diag(c: list[int], model: Model, cores: dict, orders: list[int]):
    import mpmath as mp
    mp.mp.dps=70
    a=mp.mpf(model.a); mu=mp.mpf(model.lam(1)+model.weight(2))
    rows=[]
    for n in orders:
        nmp=mp.mpf(n)
        r=mp.findroot(lambda r: mp.log(r)+mp.log1p(r)+2*r-mp.log(a*nmp),(mp.mpf('0.1'),max(mp.mpf('1'),mp.log(nmp)/2)))
        k=nmp*r/(1+r)
        logS=k*(1+2*r)-mp.log(1+4*r+2*r*r)/2
        vn=mp.mpf(c[n])/mp.factorial(n)
        pred=-mp.exp(logS-mu*r/a)
        row={'n':n,'r':mp.nstr(r,18),'v_over_leading':mp.nstr(vn/pred,18)}
        for M,(q,h) in cores.items():
            A=-mp.mpf(h[n])/mp.factorial(n)
            ell=M+1
            while model.weight(ell)==0: ell+=1
            eta=model.weight(ell)*nmp/(1+r)*(r*(1+r)/(a*nmp))**(ell-1)
            row[f'M{M}_minus_v_over_A']=mp.nstr(-vn/A,18)
            row[f'M{M}_defect_over_eta']=mp.nstr((1+vn/A)/eta,18)
        rows.append(row)
    return rows


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--order',type=int,default=240)
    ap.add_argument('--out',type=Path,default=Path(__file__).resolve().parent)
    ap.add_argument('--a',type=int,default=1)
    ap.add_argument('--cores',type=int,nargs='*',default=[2,3])
    args=ap.parse_args()
    N=args.order
    if N<20: raise SystemExit('Use --order at least 20 for the standard audit')
    args.out.mkdir(parents=True,exist_ok=True)
    model=Model(args.a)
    start=perf_counter()
    c=inverse_egf(N,model)
    cores={M:inverse_egf(N,model,M) for M in args.cores}
    assertions=0
    for n in range(1,17):
        assert partition_inverse(n,model)==c[n];assertions+=1
        for M,pair in cores.items():
            v=partition_inverse(n,model,M)
            assert v[0]==pair[0][n];assertions+=1
            assert v[1]==pair[1][n];assertions+=1
    residual=formal_composition_check(c,model,20)
    for n,x in enumerate(residual):
        assert x==(1 if n==1 else 0);assertions+=1
    # A changed early slope and weight, without changing mu=lambda_1+w_2.
    pert=Model(args.a,slopes=((2,4*args.a+1),),weights=((3,2),))
    cp=inverse_egf(min(N,120),pert)
    for n in range(1,17):
        assert partition_inverse(n,pert)==cp[n];assertions+=1
    for n,x in enumerate(formal_composition_check(cp,pert,16)):
        assert x==(1 if n==1 else 0);assertions+=1
    orders=[n for n in [20,40,80,120,160,240,300,400,600,800] if n<=N]
    if N not in orders: orders.append(N)
    rows=diag(c,model,cores,orders)
    with (args.out/'diagnostics.csv').open('w',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=list(rows[0]));writer.writeheader();writer.writerows(rows)
    data={'normalization':'n! times ordinary coefficient','a':args.a,'order':N,
          'inverse':[str(x) for x in c],
          'cores':{str(M):{'Q':[str(x) for x in q],'linear_marker':[str(x) for x in h]} for M,(q,h) in cores.items()},
          'modified_model':{'slopes':list(pert.slopes),'weights':list(pert.weights),'inverse':[str(x) for x in cp]}}
    (args.out/'exact_coefficients.json').write_text(json.dumps(data,indent=2)+'\n')
    report={'exact_assertions_passed':assertions,'order':N,'models':2,
            'elapsed_seconds':round(perf_counter()-start,3),
            'all_inverse_coefficients_negative_from_2_through_N':all(x<0 for x in c[2:]),
            'note':'Finite checks are not proofs of asymptotic limits. Diagnostics use 70-digit mpmath, not intervals.'}
    (args.out/'audit_report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
    for row in rows: print(row)

if __name__=='__main__': main()
