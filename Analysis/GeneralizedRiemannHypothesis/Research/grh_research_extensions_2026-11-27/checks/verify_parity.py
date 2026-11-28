#!/usr/bin/env python3
"""Exact finite-sample verification of the parity-profile theorem.

Counts are computed with Python integers, never Monte Carlo. Uniform-fibre
total variation is computed as an exact Fraction. Decimal comparisons to
the conditioned iid model and Gaussian profile are numerical diagnostics.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
from functools import lru_cache
from itertools import combinations
from math import comb, erf, exp, lgamma, log, log1p, sqrt
from pathlib import Path
import hashlib
import json


def multiply_truncated(a, b, degree):
    out = [0] * (min(degree, len(a) + len(b) - 2) + 1)
    for i, x in enumerate(a):
        if not x:
            continue
        for j in range(min(len(b), len(out) - i)):
            out[i + j] += x * b[j]
    return out


class ExactParityCounts:
    def __init__(self, r, n, maximum_s):
        self.r, self.n = r, n
        self.even_powers = self.odd_powers = None
        if n >= 4:
            degree = maximum_s // 2
            even = [comb(n, 2*j) for j in range(n//2 + 1)]
            odd = [comb(n, 2*j + 1) for j in range((n-1)//2 + 1)]
            self.even_powers, self.odd_powers = [[1]], [[1]]
            for j in range(r):
                self.even_powers.append(multiply_truncated(self.even_powers[-1], even, degree))
                self.odd_powers.append(multiply_truncated(self.odd_powers[-1], odd, degree))

    def counts(self, s):
        r, n = self.r, self.n
        result = [0] * (r + 1)
        for k in range(s % 2, min(r, s) + 1, 2):
            w = (s-k)//2
            if n == 1:
                val = int(k == s)
            elif n == 2:
                val = 2**k * comb(r-k, w) if 0 <= w <= r-k else 0
            elif n == 3:
                val = sum(comb(k, j) * 3**(k-j) * comb(r-k, w-j) * 3**(w-j)
                          for j in range(max(0, w-(r-k)), min(k, w)+1))
            else:
                ep, op = self.even_powers[r-k], self.odd_powers[k]
                val = sum(op[j] * ep[w-j]
                          for j in range(max(0, w-len(ep)+1), min(w, len(op)-1)+1))
            result[k] = comb(r, k) * val
        assert sum(result) == comb(r*n, s), (r, n, s, 'total count')
        return result


def statistics(r, n, s, counts):
    m = r*n
    den = comb(m, s)
    uniform_den = 2**(r-1)
    tv_numerator = sum(abs(x*uniform_den - (comb(r,k) if k % 2 == s % 2 else 0)*den)
                       for k, x in enumerate(counts))
    tv_exact = Fraction(tv_numerator, 2 * den * uniform_den)
    t = (m-2*s)/m
    a = t**n
    lam = sqrt(r)*a
    eta = (-1)**s
    q = []
    for k in range(r+1):
        if k % 2 != s % 2:
            q.append(0.0)
        elif a == 1:
            q.append(float(k == 0))
        else:
            lq = lgamma(r+1)-lgamma(k+1)-lgamma(r-k+1)
            lq += k*log1p(-a)+(r-k)*log1p(a)-(r-1)*log(2)
            lq -= log1p(eta * a**r)
            q.append(exp(lq))
    assert abs(sum(q)-1) < 1e-9
    pi = [x/den for x in counts]
    tv_iid = 0.5*sum(abs(x-y) for x,y in zip(pi,q))
    profile = erf(lam/(2*sqrt(2)))
    return dict(r=r,n=n,m=m,s=s,parity=s%2,a=a,lambda_parameter=lam,
                tv_uniform=float(tv_exact),tv_uniform_exact=str(tv_exact),
                tv_conditioned_iid=tv_iid,gaussian_profile=profile,
                profile_error=float(tv_exact)-profile,
                count_sha256=hashlib.sha256(json.dumps(counts).encode()).hexdigest())


def brute_force_checks():
    tested = 0
    for n in [1,2,3,4]:
        for r in range(2,5):
            m = r*n
            engine = ExactParityCounts(r,n,m//2)
            for s in range(m//2+1):
                enumerated = [0]*(r+1)
                for subset in combinations(range(m),s):
                    occ = [0]*r
                    for slot in subset:
                        occ[slot//n] += 1
                    enumerated[sum(x%2 for x in occ)] += 1
                assert engine.counts(s) == enumerated
                tested += 1
    return tested


def main():
    parser = argparse.ArgumentParser()
    root = Path(__file__).resolve().parent.parent
    parser.add_argument('--output',type=Path,default=root/'verification')
    parser.add_argument('--figures',type=Path,default=root/'figures')
    args = parser.parse_args()
    args.output.mkdir(parents=True,exist_ok=True)
    args.figures.mkdir(parents=True,exist_ok=True)
    checked = brute_force_checks()
    rows = []
    target_lambda = [0.0,0.125,0.25,0.5,0.75,1.0,1.5,2.0,3.0,4.0]
    settings = [(64,2),(256,2),(1024,2),(32,3),(128,3),(512,3),(16,64),(32,64),(64,64),(128,64)]
    for r,n in settings:
        samples = sorted(set(round(r*n/2*(1-(lam/sqrt(r))**(1/n)))
                             if lam else r*n//2 for lam in target_lambda if lam < sqrt(r)))
        # For large capacities omit lambda=0: near-half sampling creates unnecessarily
        # large polynomial tables. The central asymptotic is checked at n=2,3.
        if n >= 4:
            samples = [s for s in samples if s < r*n/4]
        engine = ExactParityCounts(r,n,max(samples))
        for s in samples:
            counts = engine.counts(s)
            rows.append(statistics(r,n,s,counts))
        print(f'checked r={r}, n={n}, sample sizes={len(samples)}',flush=True)
    output = dict(method='Exact integer binomial-parity counts; no Monte Carlo',
                  brute_force_parameter_cases=checked,
                  all_count_sums_verified=True,rows=rows,
                  warning='Finite examples are diagnostics, not substitutes for the proof.')
    (args.output/'parity_verification.json').write_text(json.dumps(output,indent=2)+'\n')
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    import numpy as np
    fig,axes=plt.subplots(1,3,figsize=(12,3.65),sharex=True,sharey=True)
    x=np.linspace(0,4,300)
    y=np.array([erf(z/(2*sqrt(2))) for z in x])
    for ax,n in zip(axes,[2,3,64]):
        ax.plot(x,y,color='#111827',lw=2,label='Gaussian limit')
        rr=sorted({row['r'] for row in rows if row['n']==n})
        for r in rr:
            data=sorted([row for row in rows if row['n']==n and row['r']==r],key=lambda row:row['lambda_parameter'])
            ax.plot([z['lambda_parameter'] for z in data],[z['tv_uniform'] for z in data],
                    'o-',ms=3.5,lw=1,label=f'r = {r}')
        ax.set_title(f'{n} slots per block')
        ax.set_xlabel(r'$\lambda=\sqrt{r}(1-2s/(rn))^n$')
        ax.grid(alpha=.18)
        ax.set_xlim(0,4);ax.set_ylim(0,1)
        ax.legend(fontsize=7,loc='lower right')
    axes[0].set_ylabel('Total variation from parity-uniform')
    fig.suptitle('Exact finite-population counts and the limiting parity profile',fontsize=12)
    fig.tight_layout()
    fig.savefig(args.figures/'parity_profile.png',dpi=180)
    fig.savefig(args.figures/'parity_profile.pdf')
    print(json.dumps({'brute_force_cases':checked,'profile_cases':len(rows),
                      'max_iid_error':max(row['tv_conditioned_iid'] for row in rows)}))

if __name__=='__main__':
    main()
