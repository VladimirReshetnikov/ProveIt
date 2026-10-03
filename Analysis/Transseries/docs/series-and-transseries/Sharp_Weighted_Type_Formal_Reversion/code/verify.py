#!/usr/bin/env python3
"""Exact finite checks for Sharp Weighted Type Under Formal Reversion.

Python standard library only. Computations test finite identities and inequalities;
they do not prove the limiting theorems. No network or upstream writes occur.
"""
from __future__ import annotations
import argparse
import csv
import json
import math
import random
from fractions import Fraction as F
from pathlib import Path


def mul(a: list[F], b: list[F], n: int) -> list[F]:
    c = [F(0)] * (n + 1)
    for i, ai in enumerate(a[:n+1]):
        if ai:
            for j, bj in enumerate(b[:n+1-i]):
                if bj:
                    c[i+j] += ai*bj
    return c


def compose(a: list[F], b: list[F], n: int) -> list[F]:
    if b[0]:
        raise ValueError('The inner series must have zero constant term.')
    out = [F(0)]*(n+1)
    power = [F(1)] + [F(0)]*n
    for k in range(min(n, len(a)-1)+1):
        if a[k]:
            out = [x+a[k]*y for x,y in zip(out,power)]
        power = mul(power,b,n)
    return out


def inverse_lagrange(a: list[F], n: int) -> list[F]:
    """Finite Lagrange calculation, independent of recursive composition."""
    if a[0] or not a[1]:
        raise ValueError('Reversion requires a[0]=0 and a[1]!=0.')
    slope = a[1]
    aa = [x/slope for x in a]
    h = [F(0)] + aa[2:]
    out = [F(0), F(1)/slope]
    for N in range(2,n+1):
        p = [F(1)]
        for m in range(1,N):
            p.append(sum((F(((1-N)*k-m))*h[k]*p[m-k]
                          for k in range(1,m+1)),F(0))/m)
        out.append(p[N-1]/N/slope**N)
    return out


def feedback(slopes: list[F], n: int) -> list[F]:
    """Solve U=sum q^j exp(lambda_j U), by exponential recurrences."""
    u = [F(0)]*(n+1)
    e = [[F(1)] + [F(0)]*n for _ in range(n+1)]
    for m in range(1,n+1):
        u[m] = sum((e[j][m-j] for j in range(1,m+1)),F(0))
        for j in range(1,n-m+1):
            e[j][m] = slopes[j]*sum((F(k)*u[k]*e[j][m-k]
                                     for k in range(1,m+1)),F(0))/m
    return u


def inverse_kernel_residual(q: list[F], slopes: list[F], n: int) -> list[F]:
    total = [F(0)]*(n+1)
    power = [F(1)]+[F(0)]*n
    for j in range(1,n+1):
        power = mul(power,q,n)
        exponential = [slopes[j]**k/F(math.factorial(k)) for k in range(n+1)]
        term = mul(power,exponential,n)
        total = [a+b for a,b in zip(total,term)]
    total[1] -= 1
    return total


def compositions(total: int, length: int):
    if length == 1:
        if total >= 1:
            yield (total,)
        return
    for first in range(1,total-length+2):
        for rest in compositions(total-first,length-1):
            yield (first,)+rest


def finite_bound(n: int, weights: list[F], C: F, A: F) -> F:
    D = C*A
    return A**(n-1)/n*sum((
        F(math.comb(n+k-1,k)*math.comb(n-2,k-1))*D**k
        *weights[n-k+1]*weights[2]**(k-1)
        for k in range(1,n)),F(0))


def log_fraction(x: F) -> float:
    if not x:
        return float('-inf')
    return math.log(abs(x.numerator))-math.log(x.denominator)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--order',type=int,default=70)
    args = parser.parse_args()
    N=args.order
    if not 12 <= N <= 160:
        raise SystemExit('--order must be between 12 and 160.')
    root=Path(__file__).resolve().parents[1]
    data=root/'data'; data.mkdir(exist_ok=True)
    checks: dict[str,object] = {'order':N,'seed':20260929,
        'arithmetic':'fractions.Fraction (exact rational)',
        'scope':'finite checks only, not an asymptotic proof'}
    lam=[F(j*j) for j in range(N+1)]
    u=feedback(lam,N)
    q=inverse_lagrange(u,N)
    K=min(N,30)
    identity=[F(0),F(1)]+[F(0)]*(K-1)
    assert compose(u,q,K)==identity
    assert compose(q,u,K)==identity
    assert not any(inverse_kernel_residual(q,lam,K))
    checks['quadratic_both_inverse_compositions_through']=K
    checks['quadratic_literal_inverse_kernel_through']=K
    # Scale law at a non-unit linear coefficient.
    f2=[F(2)*v for v in u[:K+1]]
    inv2=inverse_lagrange(f2,K)
    assert all(inv2[n]==q[n]/F(2)**n for n in range(K+1))
    checks['linear_rescaling_identity_through']=K
    # Analytic endpoint counterexample.
    poly=[F(0),F(1),F(-1)]+[F(0)]*(K-2)
    cat=inverse_lagrange(poly,K)
    assert all(cat[n]==F(math.comb(2*n-2,n-1),n) for n in range(1,K+1))
    checks['Catalan_endpoint_counterexample_through']=K
    rng=random.Random(20260929)
    inequalities=0; concentration=0; cases=0
    for name,weight in [
        ('factorial',lambda n: F(math.factorial(n))),
        ('factorial_squared',lambda n: F(math.factorial(n)**2)),
        ('superfactorial',lambda n: F(2**(n*n))),
        ('slow_logconvex',lambda n: F(math.prod(1+(k.bit_length()) for k in range(1,n+1))))
    ]:
        L=16; M=[weight(n) for n in range(L+1)]
        assert M[0]==1
        assert all(M[j]*M[j] <= M[j-1]*M[j+1] for j in range(1,L))
        for total in range(1,12):
            n=total+1
            for k in range(1,total+1):
                for parts in compositions(total,k):
                    product=math.prod(M[p+1] for p in parts)
                    assert product <= M[n-k+1]*M[2]**(k-1)
                    concentration+=1
            for ell in range(n+1):
                # Avoid roots: (M[n]/M[n-ell])^n >= M[n]^ell.
                assert (M[n]/M[n-ell])**n >= M[n]**ell
        for repetition in range(3):
            A=F(3,2); C=F(2)
            a=[F(0),F(1)]+[F(rng.randint(-20,20),20)*C*A**n*M[n]
                               for n in range(2,L+1)]
            b=inverse_lagrange(a,L)
            assert compose(a,b,L)==[F(0),F(1)]+[F(0)]*(L-1)
            for n in range(2,L+1):
                assert abs(b[n]) <= finite_bound(n,M,C,A)
                inequalities+=1
            cases+=1
    checks['random_signed_series_cases']=cases
    checks['exact_inverse_majorant_inequalities']=inequalities
    checks['exact_weight_concentration_inequalities']=concentration
    checks['weight_geometric_mean_checks']='passed for four weights through n=12'
    # Analytic pre/postcomposition example and its inverse factorization.
    H=[F(0)]+[F(1)]*K  # H(z)=z/(1-z)
    Hinv=[F(0)]+[F((-1)**(j-1)) for j in range(1,K+1)]
    composed=compose(H,u,K)
    invcomposed=inverse_lagrange(composed,K)
    expected=compose(q,Hinv,K)
    assert invcomposed==expected
    checks['analytic_postcomposition_inverse_factorization_through']=K
    # ed. (2026-09-29): LF rows on every platform (csv defaults to CRLF); LF text on Windows
    with (data/'quadratic_coefficients.csv').open('w',newline='') as f:
        wr=csv.writer(f,lineterminator='\n'); wr.writerow(['n','U_n','Q_n'])
        wr.writerows((n,str(u[n]),str(q[n])) for n in range(1,N+1))
    with (data/'type_diagnostics.csv').open('w',newline='') as f:
        wr=csv.writer(f,lineterminator='\n'); wr.writerow(['n','forward_refined_root','inverse_refined_root','Q_sign'])
        for n in range(3,N+1):
            # Weight (n!)/(log(n+e))^(2n); floating point diagnostics only.
            shift=-math.lgamma(n+1)/n+2*math.log(math.log(n+math.e))
            uu=math.exp(log_fraction(u[n])/n+shift)
            qq=math.exp(log_fraction(q[n])/n+shift) if q[n] else 0.0
            wr.writerow([n,format(uu,'.12g'),format(qq,'.12g'),(q[n]>0)-(q[n]<0)])
    rows=[]
    for n in range(1,11):
        rows.append(f'{n} & ${u[n]}$ & ${q[n]}$ \\\\')
    (data/'coefficient_table.tex').write_text('\n'.join(rows)+'\n',newline='\n')
    checks['diagnostics']='ordinary floating point; not interval certificates'
    checks['all_checks_passed']=True
    (data/'verification.json').write_text(json.dumps(checks,indent=2)+'\n',newline='\n')
    print(json.dumps(checks,indent=2))

if __name__=='__main__':
    main()
