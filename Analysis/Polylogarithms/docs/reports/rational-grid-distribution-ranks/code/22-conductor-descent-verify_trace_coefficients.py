#!/usr/bin/env python3
"""Exact finite Taylor checks, not numerical evaluation of polylogarithms."""
from __future__ import annotations
import json
from pathlib import Path
import sympy as s

ROOT = Path(__file__).resolve().parents[1]


def multiply_truncated(a: list, b: list, order: int) -> list:
    return [s.expand(sum(a[j]*b[n-j] for j in range(n+1)
                         if j < len(a) and n-j < len(b)))
            for n in range(order+1)]


def main() -> None:
    gamma, gamma1, L = s.symbols('gamma gamma1 L')
    checks = []
    for q in (6, 12, 30, 60, 210, 2310):
        factors = s.factorint(q)
        primes = list(factors)
        logs = {p: s.Symbol(f'log{p}') for p in primes}
        r = len(primes)
        logq = sum(factors[p]*logs[p] for p in primes)
        S1, S2 = sum(logs.values()), sum(x*x for x in logs.values())
        C = (-1)**r*s.prod(logs.values())
        # Factor out C*eps**(r-1) from the product containing zeta's pole.
        # Each (1-exp(eps*ell))/(-eps*ell) has coefficients 1, ell/2, ell**2/6.
        coeff = [s.S.One, s.S.Zero, s.S.Zero]
        for ell in logs.values():
            coeff = multiply_truncated(coeff, [1, ell/2, ell**2/6], 2)
        coeff = multiply_truncated(coeff, [1, -logq, logq**2/2], 2)
        coeff = multiply_truncated(coeff, [1, gamma, -gamma1], 2)
        expected = [1, gamma-logq+S1/2,
                    -gamma1+gamma*(S1/2-logq)+(S1/2-logq)**2/2+S2/24]
        assert all(s.expand(x-y) == 0 for x, y in zip(coeff, expected))
        checks.append(dict(q=q,prime_factors=primes,
                           vanishing_order=r-1,
                           normalized_coefficients=[str(x) for x in coeff],
                           first_three_trace_derivatives=[
                               str(s.factorial(r-1+j)*C*coeff[j]) for j in range(3)],
                           passed=True))
    L5, L13 = s.symbols('log5 log13')
    # q=260, f=4: B(1+eps)=65**(-eps)*(1-5**eps)*(1-13**eps).
    zero_factor_5 = [0, -L5, -L5**2/2]
    zero_factor_13 = [0, -L13, -L13**2/2]
    B = multiply_truncated(zero_factor_5, zero_factor_13, 2)
    B = multiply_truncated(B, [1, -L5-L13, (L5+L13)**2/2], 2)
    assert B[0] == B[1] == 0 and s.expand(B[2]-L5*L13) == 0
    twisted_second_jet = s.factorial(2)*B[2]*s.I*s.pi/2
    assert s.expand(twisted_second_jet-s.I*s.pi*L5*L13) == 0
    report = dict(arithmetic='exact finite polynomial arithmetic',
                  principal_checks=checks,
                  chi4_level260=dict(multiplier_coefficients=[str(x) for x in B],
                                     trace_second_derivative=str(twisted_second_jet),
                                     full_trace_numerically_evaluated=False,
                                     passed=True),
                  all_passed=True)
    (ROOT/'certificates/trace_coefficients.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: six principal trace expansions through two post-leading orders; '
          'twisted level-260 leading coefficient.')

if __name__ == '__main__':
    main()
