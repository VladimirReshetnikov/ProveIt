#!/usr/bin/env python3
"""High-precision inverse diagnostics; decimals are NOT interval certificates."""
from pathlib import Path
from math import factorial, comb
from fractions import Fraction as Q
import csv
import mpmath as mp
from local_expansions import corrections, eval_poly

mp.mp.dps=100

def mpq(x):
    return mp.mpf(x.numerator)/x.denominator

def main():
    rows=[]
    for theta in (1,2):
        B=corrections([Q(1,2)],[Q(1,2)],theta,3)
        c=[eval_poly(p,-1) for p in B]
        psi1=c[1];psi2=c[2]-c[1]**2/2
        psi3=c[3]-c[1]*c[2]+c[1]**3/3
        h1=psi1-Q(1,24)
        h2=psi2+psi1/2
        h3=psi3+psi2+psi1/4+Q(7,2880)
        for n in (20,40,80,160,320):
            m=n//2
            A=sum((-theta)**k*comb(m,k)**2*factorial(k)*factorial(n-2*k) for k in range(m+1))
            L=mp.log(A)+mp.mpf(theta)/4-mp.log(2*mp.pi)/2
            Y=L/mp.lambertw(L/mp.e); ell=mp.log(Y)
            n0=Y-mp.mpf('0.5')
            n1=n0-mpq(h1)/(Y*ell)
            n3=n1-mpq(h2)/(Y**2*ell)-(mpq(h3)/ell+mpq(h1)**2/ell**2+mpq(h1)**2/(2*ell**3))/Y**3
            rows.append([theta,n,mp.nstr(n0-n,18),mp.nstr(n1-n,18),mp.nstr(n3-n,18)])
    path=Path(__file__).resolve().parents[1]/'data'/'inverse_diagnostics.csv'
    with path.open('w',newline='') as f:
        w=csv.writer(f);w.writerow(['theta','n','carrier_error','first_error','third_error']);w.writerows(rows)
    print('Uncertified inverse diagnostics (100-digit working precision):')
    for row in rows:print(*row)

if __name__=='__main__':main()
