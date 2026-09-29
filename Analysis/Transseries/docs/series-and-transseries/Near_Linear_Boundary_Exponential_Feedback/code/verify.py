#!/usr/bin/env python3
"""Reproduce finite algebra checks and asymptotic-normalizer diagnostics.

Exact tests use Fraction; numerical tables use mpmath, numpy, scipy.
Floating-point envelope tables are NOT outward-rounded certificates.
The resonance table evaluates the proved implicit normalizer, not the
infinite Borel transform. No numerical test proves an asymptotic theorem.
"""
from __future__ import annotations
import argparse
import json
import math
from fractions import Fraction as F
from pathlib import Path
from typing import Iterator
import mpmath as mp
import numpy as np
from scipy.optimize import brentq
from scipy.special import digamma, gammaln, logsumexp

ROOT = Path(__file__).resolve().parents[1]

def compositions(n: int, k: int) -> Iterator[tuple[int, ...]]:
    if k == 1:
        yield (n,)
    else:
        for j in range(1, n-k+2):
            for tail in compositions(n-j, k-1):
                yield (j,) + tail

def coefficients(lam: list[F], c: list[F], order: int) -> list[F]:
    """Triangular exp recurrence; all arithmetic is exact."""
    u = [F(0)]*(order+1)
    E = [[F(1)] + [F(0)]*order for _ in range(order+1)]
    for n in range(1, order+1):
        value = F(0)
        for j in range(1, n+1):
            m = n-j
            if m:
                E[j][m] = lam[j] / m * sum(
                    (r*u[r]*E[j][m-r] for r in range(1,m+1)), F(0))
            value += c[j]*E[j][m]
        u[n] = value
    return u

def length_weight(n: int, k: int, lam: list[F], c: list[F]) -> F:
    total = F(0)
    for js in compositions(n,k):
        slope = sum((lam[j] for j in js), F(0))
        weight = math.prod(c[j] for j in js)
        total += weight * slope**(k-1)
    return total / math.factorial(k)

def harmonic_slopes(order: int) -> list[F]:
    H=F(0); ans=[F(0)]
    for j in range(1,order+1):
        H += F(1,j)
        ans.append(j*H)
    return ans

def convolution(a: list[F], b: list[F], order: int) -> list[F]:
    out=[F(0)]*(order+1)
    for i,x in enumerate(a):
        for j,y in enumerate(b[:order+1-i]):
            out[i+j] += x*y
    return out

def binomial(a: F, n: int) -> F:
    v=F(1)
    for k in range(n): v *= (a-k)/(k+1)
    return v

def exact_tests(order: int) -> dict:
    lam=harmonic_slopes(order); c=[F(0)]+[F(1)]*order
    u=coefficients(lam,c,order)
    checks=0
    for n in range(1,min(order,10)+1):
        weights=[length_weight(n,k,lam,c) for k in range(1,n+1)]
        assert sum(weights,F(0))==u[n]; checks+=1
        for k,W in enumerate(weights,1):
            m=n-k+1; A=lam[m]+(k-1)*lam[1]
            ell=A**(k-1)/math.factorial(k)
            multiplicity=k if m>1 else 1
            assert multiplicity*ell <= W <= math.comb(n-1,k-1)*ell
            checks+=1
    # Test the convex extremal inequality on every composition through degree 8.
    for n in range(1, min(order, 8)+1):
        for k in range(1, n+1):
            for js in compositions(n, k):
                assert sum((lam[j] for j in js), F(0)) <= lam[n-k+1]+(k-1)*lam[1]
                checks += 1
    weighted=[F(0)]+[F(j+1,2) for j in range(1,order+1)]
    uw=coefficients(lam,weighted,order)
    for n in range(1,min(order,9)+1):
        total=F(0)
        for k in range(1,n+1):
            W=length_weight(n,k,lam,c)
            V=length_weight(n,k,lam,weighted)
            assert W / 2**(n-k) <= V <= W*2**(n-k)
            total+=V; checks+=1
        assert total==uw[n]; checks+=1
    for n in range(2,order+1):
        lo=F(0); hi=F(0)
        for k in range(1,n+1):
            m=n-k+1; A=lam[m]+k-1
            ell=A**(k-1)/math.factorial(k)
            lo=max(lo,(k if m>1 else 1)*ell)
            hi+=math.comb(n-1,k-1)*ell
        assert lo<=u[n]<=hi; checks+=1
    resonance=[]
    for m in range(2,9):
        gamma=F(m-1,m); N=9
        coeff=[F(0)]+[binomial(gamma*k,k-1)/k for k in range(1,N+1)]
        w=[F(1)]+coeff[1:]
        h=[F(0)]+coeff[1:]
        power=[F(1)]+[F(0)]*N
        wg=[F(0)]*(N+1)
        for ell in range(N+1):
            fac=binomial(gamma,ell)
            wg=[x+fac*y for x,y in zip(wg,power)]
            power=convolution(power,h,N)
        assert all(w[k]==wg[k-1] for k in range(1,N+1))
        assert coeff[m]==F(1,m); checks+=N+1
        resonance.append({'gamma':str(gamma),'critical_coefficient':str(coeff[m])})
    return {'passed':True,'exact_assertions':checks,
            'harmonic_coefficients':[str(x) for x in u[1:]],
            'resonance_identities':resonance}

def harmonic_b(n: float) -> float:
    def f(b: float) -> float:
        x=n/(1+b)
        H=digamma(x+1)+np.euler_gamma
        return b+math.log(b)-math.log(H)
    return brentq(f,1e-12,max(2.,math.log1p(math.log1p(n))+2))

def envelope_table() -> list[dict]:
    rows=[]
    for n in [100,1000,10000,100000]:
        m=np.arange(1,n+1,dtype=float); k=n-m+1
        H=np.cumsum(1/m); A=m*H+k-1
        ell=(k-1)*np.log(A)-gammaln(k+1)
        multiplicity=np.where(m>1,k,1.)
        lower=np.max(ell+np.log(multiplicity))
        upper=logsumexp(ell+gammaln(n)-gammaln(k)-gammaln(n-k+1))
        b=harmonic_b(n)
        rows.append({'n':n,'lower_log_per_n':float(lower/n),'b_n':b,
                     'upper_log_per_n':float(upper/n),
                     'lower_maximizer_scaled':float(m[np.argmax(ell+np.log(multiplicity))]*(1+b)/n)})
    return rows

def resonance_table() -> list[dict]:
    mp.mp.dps=75; rows=[]
    for m in [2,3,4]:
        gamma=mp.mpf(m-1)/m
        for exponent in [4,8,12]:
            S=mp.mpf(10)**exponent
            def eq(b): return b+mp.log(b)-(S+b-mp.log1p(b))**gamma
            initial=S**gamma
            b=mp.findroot(eq,(initial,initial*mp.mpf('1.01')),solver='secant')
            positive=mp.mpf(0)
            for k in range(1,m):
                ck=mp.binomial(gamma*k,k-1)/k
                positive += ck*S**(1-k*(1-gamma))
            log_ratio=b-positive+gamma*mp.log(S)
            rows.append({'gamma':f'{m-1}/{m}','log_t':f'10^{exponent}',
                         'normalizer_constant_ratio':mp.nstr(mp.exp(log_ratio),15),
                         'predicted_constant':mp.nstr(mp.exp(mp.mpf(1)/m),15),
                         'log_error':mp.nstr(log_ratio-mp.mpf(1)/m,15)})
    return rows

def resonance_layer_diagnostics() -> list[dict]:
    """The moving-parameter normalizer only; not a Borel-function evaluation."""
    mp.mp.dps = 100
    rows = []
    for m in (2, 3):
        S = mp.mpf(10)**24
        for theta in (mp.mpf('-0.5'), mp.mpf(0), mp.mpf('0.5')):
            gamma = 1-mp.mpf(1)/m+theta/mp.log(S)
            def eq(b):
                return b+mp.log(b)-(S+b-mp.log1p(b))**gamma
            initial = S**gamma
            b = mp.findroot(eq, (initial, initial*mp.mpf('1.01')))
            leading = sum((mp.binomial(k*gamma,k-1)/k*S**(1-k*(1-gamma))
                           for k in range(1,m)), mp.mpf(0))
            ratio = mp.exp(b+gamma*mp.log(S)-leading)
            predicted = mp.exp(mp.exp(m*theta)/m)
            rows.append({'m':m, 'theta':str(theta), 'log_t':'10^24',
                         'normalizer_ratio':mp.nstr(ratio,20),
                         'predicted_limit':mp.nstr(predicted,20)})
    return rows

def make_tables(data: dict) -> None:
    out=ROOT/'data'; out.mkdir(exist_ok=True)
    lines=[r'\begin{tabular}{rrrrr}',r'\toprule',
           r'$n$ & lower $\log u_n/n$ & $b_n$ & upper $\log u_n/n$ & scaled maximizer\\',r'\midrule']
    for r in data['envelope_diagnostics']:
        lines.append(f"{r['n']:,} & {r['lower_log_per_n']:.6f} & {r['b_n']:.6f} & {r['upper_log_per_n']:.6f} & {r['lower_maximizer_scaled']:.6f}\\\\")
    lines.extend([r'\bottomrule',r'\end{tabular}'])
    (out/'envelope_table.tex').write_text('\n'.join(lines)+'\n')
    lines=[r'\begin{tabular}{rrrr}',r'\toprule',
           r'$\gamma$ & $\log t$ & normalizer ratio & limit $e^{1/m}$\\',r'\midrule']
    for r in data['resonance_diagnostics']:
        lines.append(f"${r['gamma']}$ & ${r['log_t']}$ & {float(r['normalizer_constant_ratio']):.10f} & {float(r['predicted_constant']):.10f}\\\\")
    lines.extend([r'\bottomrule',r'\end{tabular}'])
    (out/'resonance_table.tex').write_text('\n'.join(lines)+'\n')

def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--order',type=int,default=24)
    args=parser.parse_args()
    if not 10<=args.order<=60:
        parser.error('--order must lie between 10 and 60 (exact Fraction arithmetic).')
    data={'exact_checks':exact_tests(args.order),
          'envelope_diagnostics':envelope_table(),
          'resonance_diagnostics':resonance_table(),
          'resonance_layer_diagnostics':resonance_layer_diagnostics(),
          'limitations':['Floating-point tables are not outward-rounded certificates.',
                         'Resonance diagnostics concern an implicit asymptotic normalizer, not a computed Borel sum.',
                         'The infinite asymptotic statements are proved in the manuscript, not by finite tests.']}
    (ROOT/'data').mkdir(exist_ok=True)
    (ROOT/'data'/'verification.json').write_text(json.dumps(data,indent=2)+'\n')
    make_tables(data)
    print(json.dumps({'passed':data['exact_checks']['passed'],
                      'exact_assertions':data['exact_checks']['exact_assertions'],
                      'envelopes':data['envelope_diagnostics'],
                      'resonances':data['resonance_diagnostics'],
                      'resonance_layers':data['resonance_layer_diagnostics']},indent=2))
if __name__=='__main__':
    main()
