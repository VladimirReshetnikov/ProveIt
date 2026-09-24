#!/usr/bin/env python3
"""Exact affine odd-prime digit mask; no new Pell or universal claim."""
from math import comb
from pathlib import Path
import json


def digits(n, p):
    while n:
        n, d = divmod(n, p)
        yield d


def factorial_valuation(n, p):
    result = 0
    while n:
        n //= p
        result += n
    return result


def central_valuation(n, p):
    return factorial_valuation(2*n, p)-2*factorial_valuation(n, p)


def carry_count(n, p):
    carry = total = 0
    while n or carry:
        n, d = divmod(n, p)
        carry = (2*d+carry)//p
        total += carry
    return total


def verify():
    cases = actual_binomials = accepted = 0
    domains = []
    for p, max_N in ((3, 10), (5, 6), (7, 5), (11, 4)):
        subtotal = 0
        for N in range(max_N+1):
            L = p**N
            D0 = p*p*L
            for P in range(L):
                r = D0-p*P-1
                expected = all(d <= (p-1)//2 for d in digits(P, p))
                valuation = central_valuation(r, p)
                assert valuation == carry_count(r, p) <= N+2
                assert (valuation >= N+2) == expected
                assert (p*p-p)*L < r < D0
                assert r%2 == P%2
                if p <= 7 and N <= 2:
                    value = comb(2*r, r)
                    v = 0
                    while value%p == 0:
                        value //= p
                        v += 1
                    assert v == valuation
                    actual_binomials += 1
                subtotal += 1
                accepted += expected
        cases += subtotal
        domains.append(dict(prime=p, maximum_length=max_N, complete_words=subtotal))
    # Exact arithmetic, including non-prime-power q before decoding.
    schedules = []
    for p in (3, 5, 7, 11):
        rows = [('q2', '*', 'q', 'q'), ('L', '*', 'q2', 'q2'),
                ('D0', '*', p*p, 'L'), ('scaledP', '*', p, 'P'),
                ('gap', '-', 'D0', 'scaledP'), ('r', '-', 'gap', 1)]
        for q in range(2, 30):
            L = q**4
            for P in (0, 1, L//2, L-1):
                env = dict(q=q, P=P)
                for target, op, a, b in rows:
                    av = env[a] if isinstance(a, str) else a
                    bv = env[b] if isinstance(b, str) else b
                    env[target] = av*bv if op == '*' else av-bv
                n0 = p*q*q
                assert env['D0'] == n0*n0
                assert n0 < env['r'] < n0*n0 < n0**3
                assert env['r'] == p*p*L-p*P-1
        schedules.append(dict(prime=p, operations=6, multiplications=4,
                              subtractions=2, instructions=rows))
    p, L, P = 3, 9, 3
    r = p*p*L-p*P-1
    assert central_valuation(r, p) == 4
    assert all(d <= 1 for d in digits(P, 3))
    assert not all(d <= 1 for d in digits(P, 9))
    half_adders = [(3, 0, 1, 1), (12, 9, 1, 10)]
    for A, B, S, D in half_adders:
        assert all(all(d <= 1 for d in digits(z, 3)) for z in (A, B, S, D))
        assert A+B == S+2*D
        assert A%3+B%3 != S%3+2*(D%3)
    return dict(status='ODD_PRIME_HALF_DIGIT_MASK_PASS',
                scope='Exact mask theorem and conditional arithmetic only; the odd-prime Pell kernel and a compatible universal local verifier are not supplied.',
                complete_words=cases, accepted_words=accepted,
                actual_central_binomial_checks=actual_binomials,
                domains=domains, schedules=schedules,
                grouped_radix_counterexample=dict(p=3, L=9, P=3, r=r),
                half_adder_counterexamples=half_adders,
                proof='../1980/EXPLORATION_ODD_PRIME_HALF_DIGIT_MASK.md')


if __name__ == '__main__':
    result = verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(result['status'], result['complete_words'], 'complete words;',
          result['actual_central_binomial_checks'], 'actual binomial valuations')
