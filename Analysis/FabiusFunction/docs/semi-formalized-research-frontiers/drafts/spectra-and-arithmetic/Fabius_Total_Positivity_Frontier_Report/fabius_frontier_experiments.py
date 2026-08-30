#!/usr/bin/env python3
"""Reproducible experiments for the Fabius--Rvachev frontier report.

Let Uhat(z)=prod_{j>=0} sinc(pi*z/2^j) be the Fourier transform of
Rvachev's up function and put

  H_q(x)=prod_{j>=0} sinh(q^(j/2)*sqrt(x))/(q^(j/2)*sqrt(x)).

The Fabius/Rvachev case is q=1/4 and H_{1/4}(x)=Uhat(i*sqrt(x)/pi).
Writing H_q(x)=sum a_n(q)x^n gives the exact recurrence

  n a_n = sum_{m=1}^n (-1)^(m+1) P_m(q) a_{n-m},
  P_m(q)=zeta(2m)/(pi^(2m)(1-q^m)).

The script computes exact low-order coefficients, high-precision asymptotic
data, shifted Jensen roots, and the exact binary zero-count discrepancy.
The recurrence is alternating and badly conditioned at high order, so decimal
precision is chosen proportional to the requested order.
"""
from __future__ import annotations
import argparse, csv
from pathlib import Path
from typing import Iterable
import matplotlib.pyplot as plt
import mpmath as mp
import numpy as np
import sympy as sp


def zeta_even_over_pi(m: int) -> sp.Rational:
    """Exact zeta(2m)/pi^(2m), using Bernoulli numbers."""
    if m < 1:
        raise ValueError("m must be positive")
    return sp.factor((-1)**(m+1)*sp.bernoulli(2*m)*sp.Rational(2**(2*m-1), sp.factorial(2*m)))


def exact_power_sum(m: int, q: sp.Rational=sp.Rational(1,4)) -> sp.Rational:
    return sp.factor(zeta_even_over_pi(m)/(1-q**m))


def exact_coefficients(order: int, q: sp.Rational=sp.Rational(1,4)) -> list[sp.Rational]:
    """Exact coefficients from the logarithmic-derivative recurrence."""
    a=[sp.Rational(0)]*(order+1); a[0]=sp.Rational(1)
    p=[sp.Rational(0)]+[exact_power_sum(m,q) for m in range(1,order+1)]
    for n in range(1,order+1):
        a[n]=sp.factor(sum((-1)**(m+1)*p[m]*a[n-m] for m in range(1,n+1))/n)
    return a


def mp_coefficients(order: int, q: mp.mpf) -> list[mp.mpf]:
    """High-order coefficients; 6.5 decimal digits per order is conservative."""
    mp.mp.dps=max(100,int(6.5*order))
    p=[mp.nan]+[mp.zeta(2*m)/(mp.pi**(2*m)*(1-q**m)) for m in range(1,order+1)]
    a=[mp.mpf(0)]*(order+1); a[0]=mp.mpf(1)
    for n in range(1,order+1):
        a[n]=mp.fsum([(-1)**(m+1)*p[m]*a[n-m] for m in range(1,n+1)])/n
        if not a[n]>0:
            raise ArithmeticError(f"a_{n} is not positive; increase precision")
    return a


def digit_sum(n: int) -> int:
    return n.bit_count()


def positive_zero_count(m: int) -> int:
    """sum_{k<=m}(nu_2(k)+1)=2m-s_2(m)."""
    return 2*m-digit_sum(m)


def write_exact(output: Path, order: int=12) -> list[sp.Rational]:
    a=exact_coefficients(order)
    rows=[]
    for n,an in enumerate(a):
        c=sp.factor(an*sp.factorial(2*n)/4**n)  # even up moment
        gamma=sp.factor(sp.factorial(n)*an)     # multiplier sequence
        rows.append((n,an,c,gamma))
    with (output/'exact_coefficients.csv').open('w',newline='',encoding='utf-8') as f:
        w=csv.writer(f); w.writerow(['n','a_n','c_n','gamma_n=n!*a_n'])
        w.writerows([[str(x) for x in row] for row in rows])
    with (output/'exact_coefficients_table.tex').open('w',encoding='utf-8') as f:
        f.write('% Generated automatically.\n\\begin{tabular}{rlll}\n\\toprule\n')
        f.write('$n$ & $a_n$ & $c_n$ & $\\gamma_n=n!a_n$ \\\\\n\\midrule\n')
        for n,an,c,g in rows[:5]:
            f.write(f'{n} & $\\displaystyle {sp.latex(an)}$ & $\\displaystyle {sp.latex(c)}$ & $\\displaystyle {sp.latex(g)}$ \\\\\n')
        f.write('\\bottomrule\n\\end{tabular}\n')
    return a


def write_asymptotics(output: Path, order: int, q0: float) -> list[mp.mpf]:
    q=mp.mpf(str(q0)); a=mp_coefficients(order,q)
    sigma=1/(1-mp.sqrt(q))
    root_limit=mp.e**2*sigma**2/4
    ratio_limit=sigma**2/4
    ns=np.arange(2,order,dtype=int); roots=[]; ratios=[]
    with (output/'coefficient_asymptotics.csv').open('w',newline='',encoding='utf-8') as f:
        w=csv.writer(f); w.writerow(['n','n^2*a_n^(1/n)','root_limit','n^2*a_(n+1)/a_n','ratio_limit'])
        for n in ns:
            r=n*n*mp.power(a[n],mp.mpf(1)/n); rr=n*n*a[n+1]/a[n]
            roots.append(float(r)); ratios.append(float(rr))
            w.writerow([n,mp.nstr(r,35),mp.nstr(root_limit,35),mp.nstr(rr,35),mp.nstr(ratio_limit,35)])
    plt.figure(figsize=(7.2,4.4)); plt.plot(ns,roots,label=r'$n^2a_n^{1/n}$')
    plt.axhline(float(root_limit),linestyle='--',label='proved limit'); plt.xlabel('n'); plt.ylabel('normalization')
    plt.title(f'Coefficient root asymptotics, q={q0:g}'); plt.legend(); plt.tight_layout()
    plt.savefig(output/'coefficient_root_asymptotics.png',dpi=180); plt.close()
    plt.figure(figsize=(7.2,4.4)); plt.plot(ns,ratios,label=r'$n^2a_{n+1}/a_n$')
    plt.axhline(float(ratio_limit),linestyle='--',label='proved limit'); plt.xlabel('n'); plt.ylabel('normalization')
    plt.title(f'Coefficient ratio experiment, q={q0:g}'); plt.legend(); plt.tight_layout()
    plt.savefig(output/'coefficient_ratio_asymptotics.png',dpi=180); plt.close()
    return a


def write_zero_count(output: Path, maximum: int=4096) -> None:
    m=np.arange(1,maximum+1,dtype=int); d=np.array([-digit_sum(int(k)) for k in m])
    with (output/'zero_counting.csv').open('w',newline='',encoding='utf-8') as f:
        w=csv.writer(f); w.writerow(['M','N_plus(M)=2M-s_2(M)','N_plus-2M'])
        w.writerows([[int(k),positive_zero_count(int(k)),int(dd)] for k,dd in zip(m,d)])
    plt.figure(figsize=(7.2,4.4)); plt.plot(m,d,linewidth=.8); plt.xlabel('M')
    plt.ylabel(r'$N_+(M)-2M=-s_2(M)$'); plt.title('Binary discrepancy of the positive zero count')
    plt.tight_layout(); plt.savefig(output/'zero_count_binary_discrepancy.png',dpi=180); plt.close()


def write_jensen_roots(output: Path, degree: int=5, last_shift: int=24) -> None:
    """High-precision roots of J_gamma^{d,n}; imaginary parts should be zero."""
    a=exact_coefficients(last_shift+degree); x=sp.symbols('x')
    with (output/'jensen_roots.csv').open('w',newline='',encoding='utf-8') as f:
        w=csv.writer(f); w.writerow(['degree','shift','root','real','imaginary'])
        for shift in [0,1,4,8,16,last_shift]:
            poly=sum(sp.binomial(degree,j)*sp.factorial(shift+j)*a[shift+j]*x**j for j in range(degree+1))
            roots=sorted(sp.nroots(poly,n=70,maxsteps=300),key=lambda z:float(sp.re(z)))
            for i,z in enumerate(roots):
                w.writerow([degree,shift,i,sp.N(sp.re(z),45),sp.N(sp.im(z),45)])


def product_check(a: list[mp.mpf], samples: Iterable[float]=(0.1,1.0,10.0), factors: int=28) -> None:
    """Independent product-versus-series check at three positive arguments."""
    for x0 in samples:
        x=mp.mpf(str(x0)); s=mp.sqrt(x)
        prod=mp.fprod([mp.sinh(s/2**j)/(s/2**j) for j in range(factors)])
        series=mp.fsum([an*x**n for n,an in enumerate(a)])
        print(f'x={x0:g}: relative product/series error = {mp.nstr(abs(prod-series)/abs(series),10)}')


def main() -> None:
    p=argparse.ArgumentParser(); p.add_argument('--output',type=Path,default=Path('numerical_output'))
    p.add_argument('--order',type=int,default=220); p.add_argument('--q',type=float,default=.25); a=p.parse_args()
    if not 0<a.q<1: p.error('--q must be in (0,1)')
    a.output.mkdir(parents=True,exist_ok=True)
    write_exact(a.output); coeff=write_asymptotics(a.output,a.order,a.q)
    write_zero_count(a.output); write_jensen_roots(a.output); product_check(coeff[:60])
    print('Wrote',a.output.resolve())

if __name__=='__main__': main()
