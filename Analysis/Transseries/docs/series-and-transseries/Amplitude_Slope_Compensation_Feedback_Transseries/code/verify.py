#!/usr/bin/env python3
"""Exact finite checks for weighted exponential-feedback transseries.

The assertions verify algebraic identities and rational certificates. They
are not proofs of the infinite-order or analytic theorems in the article.
Python 3.10+; exact part uses only the standard library.
"""
from __future__ import annotations
import argparse
import json
import math
from fractions import Fraction as F
from pathlib import Path
from typing import Iterator, Sequence


def compositions(n: int) -> Iterator[tuple[int, ...]]:
    if n == 0:
        yield ()
        return
    for first in range(1, n + 1):
        for rest in compositions(n - first):
            yield (first,) + rest


def coefficients(c: Sequence[F], lam: Sequence[F], N: int) -> list[F]:
    if N < 1 or len(c) <= N or len(lam) <= N:
        raise ValueError('Supply coefficients and slopes through N >= 1.')
    if c[1] != 1 or any(x <= 0 for x in c[1:N+1]):
        raise ValueError('Require positive amplitudes and c[1] = 1.')
    if any(x < 0 for x in lam[1:N+1]):
        raise ValueError('Slopes must be nonnegative.')
    u = [F(0) for _ in range(N+1)]
    e = [[F(0) for _ in range(N+1)] for _ in range(N+1)]
    for j in range(1, N+1):
        e[j][0] = F(1)
    for n in range(1, N+1):
        for j in range(1, n+1):
            k = n-j
            if k:
                e[j][k] = lam[j] / k * sum(
                    (m*u[m]*e[j][k-m] for m in range(1, k+1)), F(0))
        u[n] = sum((c[j]*e[j][n-j] for j in range(1, n+1)), F(0))
    return u


def lagrange_coefficient(c: Sequence[F], lam: Sequence[F], n: int) -> F:
    total = F(0)
    for js in compositions(n):
        k = len(js)
        total += math.prod(c[j] for j in js) * sum(lam[j] for j in js)**(k-1) / math.factorial(k)
    return total


def inverse_blocks(c: Sequence[F], lam: Sequence[F], N: int) -> list[F]:
    v = [F(0) for _ in range(N+1)]
    for k in range(1, N+1):
        for ms in compositions(k-1):
            ell = len(ms)
            weight = F((-1)**ell*math.comb(k+ell-1, ell), k)
            weight *= math.prod(c[m+1] for m in ms)
            frequency = sum((lam[m+1] for m in ms), F(0)) - (k+ell)*lam[1]
            for n in range(k, N+1):
                v[n] += weight * frequency**(n-k) / math.factorial(n-k)
    return v


def multiply(a: Sequence[F], b: Sequence[F], N: int) -> list[F]:
    return [sum((a[j]*b[n-j] for j in range(n+1)), F(0)) for n in range(N+1)]


def compose(a: Sequence[F], b: Sequence[F], N: int) -> list[F]:
    power = [F(1)] + [F(0)]*N
    result = [F(0)]*(N+1)
    for k in range(N+1):
        if k:
            power = multiply(power, b, N)
        for n in range(N+1):
            result[n] += a[k]*power[n]
    return result


def exp_interval(x: F, terms: int = 100) -> tuple[F, F]:
    """Rigorous rational interval for exp(x), using a positive series."""
    if x < 0:
        lo, hi = exp_interval(-x, terms)
        return 1/hi, 1/lo
    term = F(1)
    partial = term
    for k in range(1, terms+1):
        term *= x/k
        partial += term
    if x >= terms+2:
        raise ValueError('Increase terms to obtain the geometric tail bound.')
    first_omitted = term*x/(terms+1)
    tail = first_omitted/(1-x/F(terms+2))
    return partial, partial+tail


def block_interval(c: Sequence[F], lam: Sequence[F], u: F, K: int) -> tuple[F, F]:
    """Enclose the first K exact inverse blocks, including exponential error."""
    lo = hi = F(0)
    for k in range(1, K+1):
        for ms in compositions(k-1):
            ell = len(ms)
            w = F((-1)**ell*math.comb(k+ell-1, ell), k)
            w *= math.prod(c[m+1] for m in ms)*u**k
            b = sum((lam[m+1] for m in ms), F(0))-(k+ell)*lam[1]
            a, z = exp_interval(b*u)
            if w >= 0:
                lo += w*a; hi += w*z
            else:
                lo += w*z; hi += w*a
    return lo, hi


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--order', type=int, default=12)
    # ed. 2026-09-29: the default output is rerun/exact_checks.json beside code/;
    # writing the recorded data/exact_checks.json needs --overwrite-recorded.
    parser.add_argument('--output', type=Path, default=Path(__file__).resolve().parents[1]/'rerun'/'exact_checks.json')
    parser.add_argument('--overwrite-recorded', action='store_true',
                        help='allow writing the recorded data/exact_checks.json')
    args = parser.parse_args()
    recorded = Path(__file__).resolve().parents[1]/'data'/'exact_checks.json'
    if args.output.resolve() == recorded.resolve() and not args.overwrite_recorded:
        parser.error('refusing to overwrite the recorded data/exact_checks.json; '
                     'pass --overwrite-recorded or choose another --output')
    N = args.order
    if not 2 <= N <= 18:
        raise ValueError('The exhaustive composition checks require 2 <= order <= 18.')
    assertions = 0
    records = []
    for p in (2, 3, 4):
        for mode in ('unit', 'geometric', 'gaussian', 'irregular'):
            c = [F(0), F(1)]
            for j in range(2, N+1):
                exponent = 0 if mode == 'unit' else (j if mode == 'geometric' else (j*j if mode == 'gaussian' else j*j+(3 if j%3 == 0 else 0)))
                c.append(F(1, 2**exponent))
            lam = [F(0)] + [F(j**p) for j in range(1, N+1)]
            if mode == 'irregular':
                lam[1] = F(3); lam[2] = F(0)
            u = coefficients(c, lam, N)
            v = inverse_blocks(c, lam, N)
            for n in range(1, N+1):
                assert u[n] == lagrange_coefficient(c, lam, n)
                assertions += 1
            target = [F(0), F(1)] + [F(0)]*(N-1)
            for actual in (compose(u, v, N), compose(v, u, N)):
                for a, b in zip(actual, target):
                    assert a == b
                    assertions += 1
            for j in range(2, N+1):
                for m in range(N-j+1):
                    assert u[j+m] >= c[j]*lam[j]**m/math.factorial(m)
                    assertions += 1
            records.append({'p':p, 'amplitudes':mode,
                            'forward_first_6':[str(x) for x in u[1:7]],
                            'inverse_first_6':[str(x) for x in v[1:7]]})
    # Independent checks of the combinatorial mass bound C_k <= 8^k.
    for k in range(1, 101):
        mass = F(1) if k == 1 else sum((F(math.comb(k+ell-1,ell)*math.comb(k-2,ell-1), k) for ell in range(1,k)), F(0))
        assert mass <= 8**k
        assertions += 1
    # A rigorous literal inverse enclosure: Gaussian amplitude, cubic slope.
    K = 10
    c = [F(0),F(1)] + [F(1,2**(j*j)) for j in range(2,K+1)]
    lam = [F(0)] + [F(j**3) for j in range(1,K+1)]
    r = F(1,100)
    lo,hi = block_interval(c,lam,-r,K)
    _, ebound = exp_interval(2*lam[1]*r)
    t = 8*r*ebound
    assert t < F(1, 3)  # Also certifies the literal inverse branch domain.
    assertions += 1
    tail = t**(K+1)/(1-t)
    lo -= tail; hi += tail
    scale = 10**30
    lo = F((lo*scale).__floor__(), scale)
    hi = F((hi*scale).__ceil__(), scale)
    assert lo < hi < 0 and hi-lo < F(2331, 10**15)
    assertions += 1
    # Independent interval check in the literal kernel, not using block inversion.
    # On |q| <= 1/50, omitted j > 15 terms are dominated by a geometric tail.
    J = 15
    qbound = F(1, 50)
    kernel_tail = qbound**(J+1)/(1-qbound)
    residual_bounds = []
    for q in (lo, hi):
        left = right = r  # Phi(q, -r) - (-r)
        for j in range(1, J+1):
            cj = F(1) if j == 1 else F(1, 2**(j*j))
            w = cj*q**j
            a, b = exp_interval(-F(j**3)*r)
            if w >= 0:
                left += w*a
                right += w*b
            else:
                left += w*b
                right += w*a
        left -= kernel_tail
        right += kernel_tail
        residual_bounds.append((left, right))
    assert -qbound < lo < hi < qbound and residual_bounds[0][1] < 0
    assertions += 1
    assert residual_bounds[1][0] > 0
    assertions += 1
    # exp(-r) >= 1-r and the other derivative terms have modulus
    # at most sum_{j>=2} j*qbound**(j-1) = (1-qbound)**(-2)-1.
    derivative_lower = 1-r-((1-qbound)**(-2)-1)
    assert derivative_lower > 0
    assertions += 1
    residual_scale = 10**35
    lower_residual_upper = F((residual_bounds[0][1]*residual_scale).__ceil__(), residual_scale)
    upper_residual_lower = F((residual_bounds[1][0]*residual_scale).__floor__(), residual_scale)
    independent = {'terms': J, 'q_absolute_bound': str(qbound),
                   'lower_endpoint_residual_upper': str(lower_residual_upper),
                   'upper_endpoint_residual_lower': str(upper_residual_lower),
                   'kernel_derivative_lower_bound': str(derivative_lower),
                   'meaning': 'Opposite endpoint signs and a positive derivative prove a unique literal root in this interval.'}
    cert = {'u':str(-r), 'blocks':K, 'lower':str(lo), 'upper':str(hi),
            'lower_decimal':float(lo), 'upper_decimal':float(hi),
            'width_exact':str(hi-lo),
            'width_upper_decimal':math.nextafter(float(hi-lo), math.inf),
            'proof':'Rational exponential bounds plus t^(K+1)/(1-t), t=8*r*exp(2*lambda_1*r).'}
    result={'status':'passed','exact_assertions':assertions,'order':N,'cases':records,
            'rational_inverse_certificate':cert,
            'independent_literal_kernel_certificate':independent,
            'scope':'Finite exact identities and the stated rational enclosure; not asymptotic or Lean verification.'}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n', newline='\n')  # ed. 2026-09-29: LF
    print(f'{assertions} exact assertions passed; order {N}; {len(records)} models.')
    print('Certified inverse interval:',cert['lower_decimal'],cert['upper_decimal'])
    print('Certificate width:',cert['width_upper_decimal'])

if __name__ == '__main__':
    main()
