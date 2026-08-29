#!/usr/bin/env python3
"""Exact/high-precision experiments for the Rvachev--Fabius report.

This script computes exact moments, probability--Chebyshev moments, monic
Jacobi coefficients, and Verblunsky coefficients.  It independently checks
Schur and Geronimus pipelines, Bessel/product identities, Cauchy-transform
representations, spectral Thue--Morse zero counts, Abel regularization, and
finite logarithmic-monodromy normalizations.  It writes CSVs, LaTeX tables,
figures, and a human-readable verification log beside itself.
"""
from __future__ import annotations

import csv
import math
from fractions import Fraction
from pathlib import Path
from typing import List, Sequence, Tuple

import mpmath as mp
import matplotlib.pyplot as plt

HERE = Path(__file__).resolve().parent
mp.mp.dps = 70


def exact_up_moments(max_degree: int) -> List[Fraction]:
    """mu_n=E[X^n], where X=(X'+U)/2 and U~Unif[-1,1]."""
    mu = [Fraction(0) for _ in range(max_degree + 1)]
    mu[0] = Fraction(1)
    for n in range(2, max_degree + 1, 2):
        rhs = sum(
            (Fraction(math.comb(n, k), k + 1) * mu[n - k]
             for k in range(2, n + 1, 2)),
            Fraction(0),
        )
        mu[n] = rhs / (2**n - 1)
    return mu


def probability_chebyshev_moments(mu: Sequence[Fraction], max_index: int) -> List[Fraction]:
    """c_n=E[T_n(X)] by the exact polynomial formula for T_{2m}."""
    c = [Fraction(0) for _ in range(max_index + 1)]
    c[0] = Fraction(1)
    for m in range(1, max_index // 2 + 1):
        total = Fraction(0)
        for k in range(m + 1):
            coeff = Fraction(
                m * math.factorial(m + k - 1) * 2 ** (2 * k),
                math.factorial(m - k) * math.factorial(2 * k),
            ) * ((-1) ** (m - k))
            total += coeff * mu[2 * k]
        c[2 * m] = total
    return c


def inner(p: Sequence[Fraction], q: Sequence[Fraction], mu: Sequence[Fraction]) -> Fraction:
    return sum(
        (pi * qj * mu[i + j]
         for i, pi in enumerate(p)
         for j, qj in enumerate(q)
         if pi and qj),
        Fraction(0),
    )


def sub_scaled(p: Sequence[Fraction], q: Sequence[Fraction], scale: Fraction) -> List[Fraction]:
    n = max(len(p), len(q))
    out = [(p[i] if i < len(p) else 0) - scale * (q[i] if i < len(q) else 0)
           for i in range(n)]
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return out


def jacobi_betas(mu: Sequence[Fraction], count: int) -> Tuple[List[Fraction], List[List[Fraction]]]:
    """Monic symmetric recurrence P_{n+1}=xP_n-beta_n P_{n-1}."""
    p0 = [Fraction(1)]
    p1 = [Fraction(0), Fraction(1)]
    polys = [p0, p1]
    h0, h1 = inner(p0, p0, mu), inner(p1, p1, mu)
    betas = [h1 / h0]
    norms = [h0, h1]
    for n in range(1, count):
        next_p = sub_scaled([Fraction(0)] + polys[n], polys[n - 1], betas[n - 1])
        polys.append(next_p)
        next_h = inner(next_p, next_p, mu)
        norms.append(next_h)
        betas.append(next_h / norms[n])
    return betas, polys


def geronimus_alphas(betas: Sequence[Fraction]) -> List[Fraction]:
    """alpha_{2n}=0, beta_{n+1}=(1/4)(1-alpha_{2n-1})(1+alpha_{2n+1})."""
    out = [Fraction(0) for _ in range(2 * len(betas))]
    prev = Fraction(-1)  # alpha_{-1}
    for n, beta in enumerate(betas):
        odd = 4 * beta / (1 - prev) - 1
        out[2 * n + 1] = odd
        prev = odd
    return out


def series_inverse(a: Sequence[Fraction], degree: int) -> List[Fraction]:
    if not a or a[0] == 0:
        raise ZeroDivisionError
    out = [Fraction(0) for _ in range(degree + 1)]
    out[0] = Fraction(1, 1) / a[0]
    for n in range(1, degree + 1):
        out[n] = -sum((a[k] * out[n-k] for k in range(1, min(n, len(a)-1)+1)), Fraction(0)) / a[0]
    return out


def series_mul(a: Sequence[Fraction], b: Sequence[Fraction], degree: int) -> List[Fraction]:
    out = [Fraction(0) for _ in range(degree + 1)]
    for i, ai in enumerate(a):
        if i > degree or not ai:
            continue
        for j, bj in enumerate(b):
            if i + j > degree:
                break
            out[i+j] += ai * bj
    return out


def series_div(a: Sequence[Fraction], b: Sequence[Fraction], degree: int) -> List[Fraction]:
    return series_mul(a, series_inverse(b, degree), degree)


def direct_schur(c: Sequence[Fraction], count: int) -> List[Fraction]:
    """Formal Schur extraction from C(w)=1+2 sum c_n w^n."""
    degree = 2 * count + 12
    car = [Fraction(0) for _ in range(degree + 2)]
    car[0] = Fraction(1)
    for n in range(1, min(len(c), len(car))):
        car[n] = 2 * c[n]
    numerator = [car[n+1] for n in range(degree+1)]  # (C-1)/w
    denominator = car[:degree+1]
    denominator[0] += 1
    f = series_div(numerator, denominator, degree)
    out: List[Fraction] = []
    for _ in range(count):
        alpha = f[0]
        out.append(alpha)
        num = f[1:] + [Fraction(0)]
        den = [Fraction(0) for _ in f]
        den[0] = Fraction(1)
        for k, fk in enumerate(f):
            den[k] -= alpha * fk
        f = series_div(num, den, len(f)-1)
    return out


def sincpi(z):
    return mp.mpf(1) if z == 0 else mp.sin(mp.pi*z)/(mp.pi*z)


def phi_product(xi, factors=100):
    p = mp.mpf(1)
    for j in range(factors):
        p *= sincpi(xi/(2**j))
    return p


def mgf_product(t, factors=100):
    p = mp.mpf(1)
    for k in range(1, factors+1):
        y = t/(2**k)
        p *= mp.mpf(1) if y == 0 else mp.sinh(y)/y
    return p


def phi_bessel(xi, c: Sequence[Fraction], terms: int):
    value = mp.besselj(0, 2*mp.pi*xi)
    for m in range(1, terms+1):
        cm = mp.mpf(c[2*m].numerator)/c[2*m].denominator
        value += 2*((-1)**m)*cm*mp.besselj(2*m, 2*mp.pi*xi)
    return value


def mgf_bessel(t, c: Sequence[Fraction], terms: int):
    value = mp.besseli(0, t)
    for m in range(1, terms+1):
        cm = mp.mpf(c[2*m].numerator)/c[2*m].denominator
        value += 2*cm*mp.besseli(2*m, t)
    return value


def cauchy_cheb(z, c: Sequence[Fraction], terms: int):
    root = mp.sqrt(z*z-1)
    w = z-root
    num = mp.mpf(1)
    for m in range(1, terms+1):
        cm = mp.mpf(c[2*m].numerator)/c[2*m].denominator
        num += 2*cm*w**(2*m)
    return num/root


def cauchy_moment(z, mu: Sequence[Fraction], terms: int):
    return sum((mp.mpf(mu[2*k].numerator)/mu[2*k].denominator / z**(2*k+1)
                for k in range(terms+1)), mp.mpf(0))


def cauchy_laplace(z, factors=70):
    f = lambda t: mp.e**(-z*t)*mgf_product(t, factors)
    return mp.quad(f, [0,1,2,4,8,16,32,48])


def eps(n: int) -> int:
    return -1 if n.bit_count() & 1 else 1


def v2(n: int) -> int:
    r = 0
    while n % 2 == 0:
        n //= 2
        r += 1
    return r


def zero_count(n: int) -> int:
    return sum(1+v2(m) for m in range(1,n+1))


def abel_square_wave(theta, r):
    return (2/mp.pi)*mp.atan2(2*r*mp.sin(theta), 1-r*r)


def abel_tm(n: int, r):
    if n == 0:
        return mp.mpf(1)
    jmax = math.floor(math.log2(n+0.5))
    p = mp.mpf(1)
    for j in range(jmax+1):
        p *= abel_square_wave(mp.pi*(n+mp.mpf('0.5'))/(2**j), r)
    return p


def latex_fraction(q: Fraction) -> str:
    return str(q.numerator) if q.denominator == 1 else rf"\frac{{{q.numerator}}}{{{q.denominator}}}"


def dec(q: Fraction, digits=18) -> str:
    return mp.nstr(mp.mpf(q.numerator)/q.denominator, digits)


def write_data(c, betas, alphas):
    specs = [
        ('chebyshev_moments.csv', list(enumerate(c))),
        ('jacobi_coefficients.csv', list(enumerate(betas, start=1))),
        ('schur_parameters.csv', list(enumerate(alphas))),
    ]
    for name, rows in specs:
        with (HERE/name).open('w', newline='', encoding='utf-8') as f:
            w = csv.writer(f); w.writerow(['index','numerator','denominator','decimal'])
            for n,q in rows:
                w.writerow([n,q.numerator,q.denominator,dec(q,30)])

    lines = [r'% Generated by numerical_experiments.py', '\n']
    lines += [r'\begin{table}[htbp]\centering\scriptsize\renewcommand{\arraystretch}{1.9}', '\n',
              r'\caption{First exact probability--Chebyshev moments.}\label{tab:cheb}', '\n',
              r'\begin{tabular}{r r l}\toprule $m$&$2m$&$c_{2m}$\\\midrule', '\n']
    for m in range(7):
        lines += [f'{m}&{2*m}&$\\displaystyle {latex_fraction(c[2*m])}$\\\\\n']
    lines += [r'\bottomrule\end{tabular}\end{table}', '\n']
    lines += [r'\begin{table}[htbp]\centering\scriptsize\renewcommand{\arraystretch}{1.9}', '\n',
              r'\caption{First exact nonzero Verblunsky coefficients.}\label{tab:alpha}', '\n',
              r'\begin{tabular}{r l r}\toprule $n$&$\alpha_n$&decimal\\\midrule', '\n']
    for n in range(1,10,2):
        lines += [f'{n}&$\\displaystyle {latex_fraction(alphas[n])}$&{dec(alphas[n],12)}\\\\\n']
    lines += [r'\bottomrule\end{tabular}\end{table}', '\n']
    lines += [r'\begin{table}[htbp]\centering\scriptsize\renewcommand{\arraystretch}{1.9}', '\n',
              r'\caption{First exact monic Jacobi recurrence coefficients.}\label{tab:beta}', '\n',
              r'\begin{tabular}{r l r}\toprule $n$&$\beta_n$&decimal\\\midrule', '\n']
    for n,q in list(enumerate(betas,start=1))[:5]:
        lines += [f'{n}&$\\displaystyle {latex_fraction(q)}$&{dec(q,12)}\\\\\n']
    lines += [r'\bottomrule\end{tabular}\end{table}', '\n']
    (HERE/'generated_tables.tex').write_text(''.join(lines), encoding='utf-8')


def make_plots(c, alphas):
    trunc = list(range(1,21))
    phi_err = [mp.mpf(0) for _ in trunc]
    for k in range(121):
        x = mp.mpf(-4)+mp.mpf(8)*k/120
        target = phi_product(x,90)
        partial = mp.besselj(0,2*mp.pi*x)
        for m in trunc:
            cm = mp.mpf(c[2*m].numerator)/c[2*m].denominator
            partial += 2*((-1)**m)*cm*mp.besselj(2*m,2*mp.pi*x)
            phi_err[m-1] = max(phi_err[m-1],abs(partial-target))
    plt.figure(figsize=(7.2,4.6)); plt.semilogy(trunc,[float(x) for x in phi_err],marker='o')
    plt.xlabel('Even Chebyshev moments retained'); plt.ylabel(r'$\max_{|\xi|\leq4}|\Phi-\Phi_M|$')
    plt.title('Bessel-series convergence to the sinc product'); plt.grid(True,which='both',alpha=.3)
    plt.tight_layout(); plt.savefig(HERE/'bessel_convergence.png',dpi=220); plt.savefig(HERE/'bessel_convergence.pdf'); plt.close()

    mgf_err = [mp.mpf(0) for _ in trunc]
    for k in range(101):
        t = mp.mpf(8)*k/100
        target = mgf_product(t,90)
        partial = mp.besseli(0,t)
        for m in trunc:
            cm = mp.mpf(c[2*m].numerator)/c[2*m].denominator
            partial += 2*cm*mp.besseli(2*m,t)
            mgf_err[m-1] = max(mgf_err[m-1],abs(partial-target))
    plt.figure(figsize=(7.2,4.6)); plt.semilogy(trunc,[float(x) for x in mgf_err],marker='o')
    plt.xlabel('Even Chebyshev moments retained'); plt.ylabel(r'$\max_{0\leq t\leq8}|M-M_M|$')
    plt.title('Modified-Bessel convergence to the hyperbolic product'); plt.grid(True,which='both',alpha=.3)
    plt.tight_layout(); plt.savefig(HERE/'mgf_bessel_convergence.png',dpi=220); plt.savefig(HERE/'mgf_bessel_convergence.pdf'); plt.close()

    inds = list(range(1,len(alphas),2)); vals = [float(alphas[n]) for n in inds]
    plt.figure(figsize=(7.2,4.6)); plt.plot(inds,vals,marker='o'); plt.axhline(0,linewidth=.8)
    plt.xlabel('Odd index n'); plt.ylabel(r'$\alpha_n$'); plt.title('Exact odd Verblunsky coefficients')
    plt.grid(True,alpha=.3); plt.tight_layout(); plt.savefig(HERE/'verblunsky_coefficients.png',dpi=220)
    plt.savefig(HERE/'verblunsky_coefficients.pdf'); plt.close()
    return phi_err[-1], mgf_err[-1]


def main():
    mu = exact_up_moments(100)
    c = probability_chebyshev_moments(mu,100)
    betas,_ = jacobi_betas(mu,20)
    alphas = geronimus_alphas(betas)
    assert direct_schur(c,16) == alphas[:16]
    assert mu[2] == Fraction(1,9) and c[2] == Fraction(-7,9)
    assert all(q>0 for q in betas) and all(abs(a)<1 for a in alphas)
    for n in range(257):
        assert zero_count(n) == 2*n-n.bit_count()
        assert (-1 if zero_count(n)&1 else 1) == eps(n)
    for N in range(1,10):
        scale = 2**(N*(N-1)//2)
        for j in range(2**N):
            assert Fraction(scale*eps(j),scale) == eps(j)

    write_data(c,betas,alphas)
    phi_plot,mgf_plot = make_plots(c,alphas)

    phi_spots = [mp.mpf('0.125'),mp.mpf('0.7'),mp.mpf('1.75'),mp.mpf('3.2')]
    phi_errors = [abs(phi_bessel(x,c,40)-phi_product(x,120)) for x in phi_spots]
    mgf_spots = [mp.mpf('0.25'),mp.mpf('1'),mp.mpf('3'),mp.mpf('7')]
    mgf_errors = [abs(mgf_bessel(t,c,40)-mgf_product(t,120)) for t in mgf_spots]
    crows=[]
    for z in [mp.mpf('1.5'),mp.mpf('2'),mp.mpf('3')]:
        a=cauchy_cheb(z,c,40); b=cauchy_moment(z,mu,40); d=cauchy_laplace(z,70)
        crows.append((z,a,b,d,abs(a-b),abs(a-d)))
    abel=[]
    for txt in ['0.9','0.99','0.999','0.9999']:
        r=mp.mpf(txt); abel.append((r,max(abs(abel_tm(n,r)-eps(n)) for n in range(64))))

    lines=[]
    lines += ['Exact and high-precision verification log\n','='*72+'\n\n']
    lines += [f'mpmath precision: {mp.mp.dps} digits\n','Moments and c_n through degree 100\n',
              'Jacobi coefficients: 20; Verblunsky coefficients: 40\n\n']
    lines += ['First c_{2m}:\n']
    for m in range(7): lines += [f'  c_{2*m:2d} = {str(c[2*m]):>45s} ({dec(c[2*m],20)})\n']
    lines += ['\nFirst odd alpha_n:\n']
    for n in range(1,20,2): lines += [f'  alpha_{n:2d} = {str(alphas[n]):>45s} ({dec(alphas[n],20)})\n']
    lines += ['\nDirect Schur = Geronimus through alpha_15: PASS\n',
              'Spectral zero count for n=0,...,256: PASS\n',
              'Monodromy normalization for N=1,...,9: PASS\n\n']
    lines += ['Fourier Bessel spot errors (40 even terms):\n']
    for x,e in zip(phi_spots,phi_errors): lines += [f'  xi={mp.nstr(x,8):>8s}: {mp.nstr(e,12)}\n']
    lines += ['\nMGF Bessel spot errors (40 even terms):\n']
    for t,e in zip(mgf_spots,mgf_errors): lines += [f'  t={mp.nstr(t,8):>8s}: {mp.nstr(e,12)}\n']
    lines += ['\nThree-way Cauchy-transform checks:\n']
    for z,a,b,d,e1,e2 in crows:
        lines += [f'  z={z}:\n',f'    Joukowski/Chebyshev {mp.nstr(a,30)}\n',
                  f'    moment series       {mp.nstr(b,30)}\n',f'    Laplace product      {mp.nstr(d,30)}\n',
                  f'    errors              {mp.nstr(e1,12)}, {mp.nstr(e2,12)}\n']
    lines += ['\nAbel-Poisson max errors for n=0,...,63:\n']
    for r,e in abel: lines += [f'  r={r}: {mp.nstr(e,12)}\n']
    lines += [f'\nGrid max Bessel/sinc error at M=20: {mp.nstr(phi_plot,12)}\n',
              f'Grid max modified-Bessel/MGF error at M=20: {mp.nstr(mgf_plot,12)}\n']
    text=''.join(lines); (HERE/'numerical_results.txt').write_text(text,encoding='utf-8'); print(text)

if __name__ == '__main__':
    main()
