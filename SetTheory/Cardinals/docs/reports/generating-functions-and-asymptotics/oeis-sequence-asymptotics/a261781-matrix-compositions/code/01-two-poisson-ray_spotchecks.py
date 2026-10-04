#!/usr/bin/env python3
"""Optional additional compact-ray checks. Requires sympy and mpmath.

Run after or independently of verify.py. These tests use exact integer T(n,k)
and the general Gaussian coefficient algorithm at ratios 3/2, 3 and 5.
They are high-precision consistency checks, not certified error bounds.
"""
from __future__ import annotations
import csv
import math
from pathlib import Path
import mpmath as mp
import verify

def main() -> None:
    mp.mp.dps=75
    N=400
    first,second=verify.stirling_tables(N)
    fac=[math.factorial(j) for j in range(N+1)]
    F=[sum(fac[j]*second[n][j] for j in range(n+1)) for n in range(N+1)]
    ps=verify.kernel_polynomials(3)
    L=mp.log(2)
    rows=[]
    for n,k in [(60,40),(150,100),(300,200),(120,40),(300,100),(200,40),(400,80)]:
        rho=mp.mpf(n)/k
        tau=mp.findroot(lambda t:t/(1-mp.exp(-t))-rho,(rho/2,rho))
        b=rho*(1+tau-rho)
        mu=L*tau/2
        A=verify.saddle_coefficients(rho,tau,3,ps)
        numerator=fac[k]*sum(first[n][j]*second[j][k]*F[j] for j in range(k,n+1))
        assert numerator%fac[n]==0
        exact=numerator//fac[n]
        B=mp.factorial(n)*mp.expm1(tau)**k*mp.exp(mu)/(2*L**(n+1)*tau**n*mp.sqrt(2*mp.pi*k*b))
        row={'n':n,'k':k,'rho':str(rho)}
        for M in range(4):
            ratio=B*sum(A[j]/mp.mpf(k)**j for j in range(M+1))/exact
            row[f'relative_error_order_{M}']=mp.nstr(ratio-1,20)
        print(row)
        rows.append(row)
    path=Path(__file__).resolve().parents[1]/'results/ray_spot_checks.csv'
    with path.open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(rows[0]))
        w.writeheader();w.writerows(rows)
    print(f'Wrote {path}')

if __name__=='__main__':
    main()
