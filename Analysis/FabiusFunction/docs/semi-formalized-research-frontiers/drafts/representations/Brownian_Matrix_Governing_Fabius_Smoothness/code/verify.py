#!/usr/bin/env python3
"""Exact convex-algebra checks and high-precision Fourier diagnostics.

Run from any directory: python code/verify.py
Only mpmath is required. The rational checks are exact. Floating-point
sinc-product calculations are diagnostics, not formal/interval certificates.
"""
from __future__ import annotations
import csv
import json
import math
import platform
import random
from fractions import Fraction as F
from pathlib import Path
from typing import Sequence
import mpmath as mp

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'data'
OUT.mkdir(exist_ok=True)


def envelope(lam: Sequence[F], s: Sequence[F]) -> F:
    """Exact integral of max(0, s_j-lambda_j*t), t>=0."""
    if not lam or len(lam) != len(s) or any(x <= 0 for x in lam):
        raise ValueError('Positive rates and equally sized nonempty vectors required')
    if any(x < 0 for x in s):
        raise ValueError('Logarithmic scales must be nonnegative')
    end = max(x / l for x, l in zip(s, lam))
    cuts = {F(0), end}
    for x, l in zip(s, lam):
        cuts.add(x/l)
    for i in range(len(lam)):
        for j in range(i):
            if lam[i] != lam[j]:
                t = (s[i] - s[j]) / (lam[i] - lam[j])
                if 0 < t < end:
                    cuts.add(t)
    cuts = sorted(x for x in cuts if 0 <= x <= end)
    area = F(0)
    for a, b in zip(cuts, cuts[1:]):
        mid = (a+b)/2
        vals = [s[j]-lam[j]*mid for j in range(len(lam))]
        j = max(range(len(lam)), key=vals.__getitem__)
        if vals[j] > 0:
            area += s[j]*(b-a) - lam[j]*(b*b-a*a)/2
    return area


def matvec(lam: Sequence[F], alpha: Sequence[F]) -> list[F]:
    return [sum(min(x,y)*a for y,a in zip(lam,alpha)) for x in lam]


def quadratic(lam: Sequence[F], alpha: Sequence[F]) -> F:
    return sum(a*s for a,s in zip(alpha,matvec(lam,alpha)))/2


def determinant(a: list[list[F]]) -> F:
    a = [row[:] for row in a]
    ans = F(1)
    for i in range(len(a)):
        j = next((j for j in range(i,len(a)) if a[j][i]), None)
        if j is None:
            return F(0)
        if j != i:
            a[i],a[j] = a[j],a[i]
            ans = -ans
        p = a[i][i]
        ans *= p
        for j in range(i+1,len(a)):
            c = a[j][i]/p
            for k in range(i+1,len(a)):
                a[j][k] -= c*a[i][k]
    return ans


def exact_tests() -> dict:
    rng = random.Random(20260929)
    trials = 1200
    for _ in range(trials):
        d = rng.randint(1,6)
        lam = sorted(F(x,7) for x in rng.sample(range(1,70),d))
        alpha = [F(rng.randrange(12), rng.randint(1,4)) for _ in lam]
        sstar = matvec(lam,alpha)
        q = quadratic(lam,alpha)
        assert envelope(lam,sstar) == q
        assert sum(a*s for a,s in zip(alpha,sstar)) == 2*q
        s = [F(rng.randrange(100),rng.randint(1,5)) for _ in lam]
        assert sum(a*t for a,t in zip(alpha,s)) - envelope(lam,s) <= q
        factor = F(rng.randint(1,8),rng.randint(1,8))
        assert envelope(lam,[factor*t for t in s]) == factor*factor*envelope(lam,s)
        tails = [sum(alpha[j:]) for j in range(d)]
        increments = [lam[0]]+[lam[j]-lam[j-1] for j in range(1,d)]
        assert q == sum(dl*n*n for dl,n in zip(increments,tails))/2
        M = [[min(x,y) for y in lam] for x in lam]
        assert determinant(M) == math.prod(increments)
        assert q <= max(lam)*sum(alpha)**2/2
    # Exact signed-parity coefficient identity, including cancellation of all odd digits.
    r = F(2,5)
    for n in range(100):
        a,b = F(7,3), F(-5,11)
        direct = a*r**n + b*(-r)**n
        parity = ((a+b)*r**n if n%2 == 0 else (a-b)*r**n)
        assert direct == parity
        assert r**n + (-r)**n == (2*r**n if n%2 == 0 else 0)
    assert envelope([F(1),F(2),F(4)],[F(5),F(8),F(12)]) == 21
    return {'rational_trials': trials, 'assertions_per_trial': 7,
            'signed_parity_trials': 100, 'total_exact_assertions': trials*7+100*2+1,
            'status': 'all exact assertions passed'}


def log_product(q: Sequence[mp.mpf], a: Sequence[mp.mpf], tol: mp.mpf) -> tuple[mp.mpf,mp.mpf,int]:
    """Log absolute sinc product plus an analytic bound on the omitted log tail.

    |log sinc u| <= u^2/5 for |u|<=1. The bound is an analytic truncation
    bound evaluated in floating point, not a rounding-error enclosure.
    """
    b = list(a)
    r = max(abs(t) for t in q)
    total = mp.mpf('0')
    for n in range(10000):
        B = sum(abs(t) for t in b)
        tail = B*B/(5*(1-r*r))
        if B <= 1 and tail < tol:
            return total, tail, n
        u = sum(b)
        if u:
            sine = mp.sin(u)
            if not sine:
                return mp.ninf, tail, n
            total += mp.log(abs(sine/u))
        b = [t*z for t,z in zip(b,q)]
    raise RuntimeError('Tail budget not met')


def diagnostics() -> dict:
    mp.mp.dps = 160
    rng = random.Random(7292026)
    lam = [mp.mpf(1),mp.mpf(2),mp.mpf(4)]
    q = [mp.exp(-x) for x in lam]
    logW = sum(mp.log(2/(1-abs(x))) for x in q)
    samples = 96
    rows=[]
    worst_tail=mp.mpf(0)
    for k in (1,2,4,8,16):
        alpha=[2*k,k,2*k]
        s=[5*k,8*k,12*k]
        H=mp.mpf(21*k*k)
        logs=[]
        witnesses=[]
        for _ in range(samples):
            r=[1+mp.mpf(rng.randrange(1,10**12))/10**12 for _ in lam]
            a=[mp.exp(x)*y for x,y in zip(s,r)]
            value,tail,_=log_product(q,a,mp.mpf('1e-90'))
            worst_tail=max(worst_tail,tail)
            logs.append(value)
            witnesses.append(sum(n*mp.log(t) for n,t in zip(alpha,a))+value-tail-logW)
        row={'k':k,'total_order':sum(alpha),'H_and_Q':str(H),
             'mean_log_product':mp.nstr(sum(logs)/samples,25),
             'max_log_product':mp.nstr(max(logs),25),
             'mean_error_over_max_scale':mp.nstr((sum(logs)/samples+H)/max(s),15),
             'best_log_derivative_lower_witness':mp.nstr(max(witnesses),25),
             'witness_minus_Q_over_order':mp.nstr((max(witnesses)-H)/sum(alpha),15)}
        rows.append(row)
    with (OUT/'box_diagnostics.csv').open('w',newline='') as fp:
        w=csv.DictWriter(fp,fieldnames=rows[0]);w.writeheader();w.writerows(rows)
    rayrows=[]
    qray=[mp.mpf('0.5'),mp.mpf('0.25')]
    for theta in ([1,1],[0,1]):
        rate=mp.log(2) if theta[0] else mp.log(4)
        for L in (8,16,32,64):
            logs=[]
            for _ in range(samples):
                r=1+mp.mpf(rng.randrange(1,10**12))/10**12
                a=[r*mp.exp(L)*t for t in theta]
                value,tail,_=log_product(qray,a,mp.mpf('1e-90'))
                worst_tail=max(worst_tail,tail)
                logs.append(value)
            pred=-mp.mpf(L)**2/(2*rate)
            rayrows.append({'theta':str(theta),'log_R':L,
                'quadratic_prediction':mp.nstr(pred,25),
                'max_log_product':mp.nstr(max(logs),25),
                'mean_log_product':mp.nstr(sum(logs)/samples,25),
                'max_error_over_log_R':mp.nstr((max(logs)-pred)/L,15)})
    with (OUT/'ray_diagnostics.csv').open('w',newline='') as fp:
        w=csv.DictWriter(fp,fieldnames=rayrows[0]);w.writeheader();w.writerows(rayrows)
    # Nonresonant-sign and resonance factorization checks, high precision.
    r=mp.mpf('0.4')
    factor_error=mp.mpf(0)
    for a,b in [(mp.mpf('1.37'),mp.mpf('2.19')),
                (mp.mpf('103.1'),mp.mpf('-13.7')),
                (mp.exp(20),mp.exp(20))]:
        lhs,_,_=log_product([r,-r],[a,b],mp.mpf('1e-100'))
        even,_,_=log_product([r*r],[a+b],mp.mpf('1e-100'))
        odd,_,_=log_product([r*r],[r*(a-b)],mp.mpf('1e-100'))
        factor_error=max(factor_error,abs(lhs-even-odd))
    with (OUT/'numerical_table.tex').open('w') as fp:
        fp.write('\\begin{tabular}{rrrrr}\n\\toprule\n$k$ & $|\\alpha|$ & $\\Qf(\\alpha)$ & Sample mean $\\log|\\Phi|$ & Best log witness\\\\\n\\midrule\n')
        for row in rows:
            fp.write(f"{row['k']} & {row['total_order']} & {float(row['H_and_Q']):.0f} & "
                     f"{float(row['mean_log_product']):.3f} & "
                     f"{float(row['best_log_derivative_lower_witness']):.3f} \\\\\n")
        fp.write('\\bottomrule\n\\end{tabular}\n')
    return {'precision_decimal_digits':mp.mp.dps,'samples_per_box_or_ray_window':samples,
            'number_of_box_cases':len(rows),'number_of_ray_cases':len(rayrows),
            'largest_analytic_log_tail_bound':mp.nstr(worst_tail,8),
            'signed_factorization_max_log_error':mp.nstr(factor_error,8),
            'status':'diagnostics only; not interval or proof-assistant certificates'}


def main() -> None:
    if not __debug__:
        raise RuntimeError('Run without -O so the exact assertions remain enabled')
    report={'python':platform.python_version(),'mpmath':mp.__version__,
            'exact':exact_tests(),'numerical':diagnostics()}
    (OUT/'verification_report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__ == '__main__':
    main()
