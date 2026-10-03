#!/usr/bin/env python3
"""Optional high-precision demonstrations, not proof certificates.

Needs mpmath. Uses exact rational Bernoulli coefficients, but evaluates errors
numerically. Run: python asymptotic_demo.py
"""
from __future__ import annotations
import csv
import math
from fractions import Fraction as F
from pathlib import Path
from verify import ROWS, Row, value


def bernoulli(n: int) -> F:
    """Exact Bernoulli number, with B_1 = -1/2."""
    b = [F(1)]
    for j in range(1,n+1):
        b.append(-sum(F(math.comb(j+1,k))*b[k] for k in range(j))/(j+1))
    return b[n]


def gamma(row: Row, j: int) -> F:
    if j < 1 or j%2 == 0:
        return F(0)
    a=[F(row.L),F(row.c,row.d)]
    b=[F(row.A),F(row.B),F(row.c,row.d)+row.m]
    return bernoulli(j+1)/((j+1)*j)*(sum(x**(-j) for x in a)-sum(x**(-j) for x in b))


def main() -> None:
    try:
        import mpmath as mp
    except ImportError as exc:
        raise SystemExit('Optional dependency missing: install mpmath to run this demonstration.') from exc
    mp.mp.dps=90
    root=Path(__file__).resolve().parent
    def m(x):
        x=F(x)
        return mp.mpf(x.numerator)/x.denominator
    output=['Numerical demonstrations only; these do not certify real-number inequalities.',
            f'mpmath version {mp.__version__}; {mp.mp.dps} decimal digits.',
            'Columns: sequence, n, logarithmic error after gamma_3, stated bound, inverse error after N^-3']
    rows=[]
    coeffs=[]
    expected=[(F(1,18),F(-163,7776)),(F(1,12),F(-163,2304)),
              (F(1,48),F(-257,13824)),(F(-1,30),F(-337,1620000)),
              (F(19,216),F(-9131,419904))]
    for rr,want in zip(ROWS,expected):
        if (gamma(rr,1),gamma(rr,3))!=want:
            raise AssertionError('Printed asymptotic coefficient table mismatch')
        t=m(F(rr.c,rr.d))
        tau=rr.L*mp.log(rr.L)+t*mp.log(t)-rr.A*mp.log(rr.A)-rr.B*mp.log(rr.B)-(t+rr.m)*mp.log(t+rr.m)
        logK=mp.log(mp.mpf(rr.L)*t/(rr.A*rr.B*(t+rr.m)))/2-mp.log(2*mp.pi)/2
        g1,g3=m(gamma(rr,1)),m(gamma(rr,3))
        for j in range(1,12,2):
            coeffs.append([rr.oeis,j,str(gamma(rr,j))])
        for n in (10,50,200):
            exact=value(rr,n)
            logy=mp.log(exact.numerator)-mp.log(exact.denominator)
            approx=n*tau-mp.log(n)/2+logK+g1/n+g3/n**3
            err=abs(logy-approx)
            slopes=[m(rr.L),t,m(rr.A),m(rr.B),t+rr.m]
            bound=m(abs(bernoulli(6))/30)*sum(x**(-5) for x in slopes)/n**5
            if err>bound*(1+mp.mpf('1e-50')):
                raise AssertionError('Numerical discrepancy with the proved remainder bound')
            N=-mp.lambertw(-2*tau*mp.exp(2*logK-2*logy),-1)/(2*tau)
            inv=N-g1/(tau*N)-g1/(2*tau**2*N**2)-(g3/tau+g1**2/tau**2+g1/(4*tau**3))/N**3
            ierr=abs(inv-n)
            vals=[rr.oeis,n,mp.nstr(err,14),mp.nstr(bound,14),mp.nstr(ierr,14)]
            rows.append(vals)
            output.append(', '.join(map(str,vals)))
    output.append('All numerical remainder comparisons passed; exact coefficient table agrees.')
    with (root/'asymptotic_results.csv').open('w',newline='') as f:
        w=csv.writer(f);w.writerow(['OEIS','n','abs_log_error','log_error_bound','abs_inverse_error']);w.writerows(rows)
    with (root/'asymptotic_coefficients.csv').open('w',newline='') as f:
        w=csv.writer(f);w.writerow(['OEIS','inverse_power','gamma_exact']);w.writerows(coeffs)
    text='\n'.join(output)+'\n'
    (root/'asymptotic_results.txt').write_text(text)
    print(text,end='')

if __name__=='__main__':
    main()
