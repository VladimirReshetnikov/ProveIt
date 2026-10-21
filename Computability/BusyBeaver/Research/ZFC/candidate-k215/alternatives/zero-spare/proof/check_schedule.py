#!/usr/bin/env python3
"""Finite arithmetic certificate for the ordinary all-natural debt-two proof.

This program does not replace the induction in report.tex. It checks every
finite premise used there, using no source interpreter, TM checker, or parent
schedule implementation. The schedule is the command-local K215 order210.
"""
from pathlib import Path
from math import isqrt
import argparse
import hashlib
import json


def pair(x, y):
    return (x + y) * (x + y + 1) // 2 + y


def unpair(n):
    diagonal = (isqrt(8 * n + 1) - 1) // 2
    second = n - diagonal * (diagonal + 1) // 2
    return diagonal - second, second


def f(n):
    return unpair(n)[1]


def descriptor(n):
    tag, y = unpair(n)
    if tag == 0:
        return 'NIP', -1, y
    if tag == 1:
        return 'DROP', 1, y
    if tag == 2:
        return 'MP', 0, f(y)
    return 'AX', 10, f(f(y))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    b, m, length, cumulative = [], [], [], []
    total, minimum, first_minimum = 0, 0, None
    early = []
    # Complete diagonals 0 through 35: the next begins at T_36 = 666.
    for n in range(666):
        name, delta, remainder = descriptor(n)
        assert pair(*unpair(n)) == n
        assert remainder == 0 or 0 <= remainder - 1 < n
        child = remainder - 1
        net = delta + (b[child] if remainder else 0)
        least = min(0, delta + (m[child] if remainder else 0))
        size = 1 + (length[child] if remainder else 0)
        assert size <= n + 1
        assert least >= -(n + 1)
        b.append(net)
        m.append(least)
        length.append(size)
        if total + least < minimum:
            minimum = total + least
            first_minimum = n
        assert total + least >= -3
        total += net
        cumulative.append(total)
        if n >= 6:
            assert total >= 7
        if n < 16:
            early.append(dict(candidate=n, command=name, remainder=remainder,
                              balance=net, minimum=least, cumulative=total))
    assert b[0] == m[0] == -1
    assert minimum == -3 and first_minimum == 5
    assert cumulative[:6] == [-1, 0, -2, -2, -2, -2]

    # Lower bound on prefix sums of g(0)=0, g(r)=b(r-1) for r>0.
    small_p = [0, -1, 0, -2, -2, -2, -2]
    def p(t):
        return small_p[t] if t < 7 else 7

    def q(t):
        a, e = unpair(t)
        d = a + e
        return sum(p(j) for j in range(d)) + p(e)

    assert sum(small_p) == -9 and min(small_p) == -2
    q45 = [q(t) for t in range(45)]
    assert min(q45) == -11
    assert sum(min(0, value) for value in q45) == -224
    # For d>=7, q(T_d+e)=7*d-58+p(e). Thus q>=7*d-60,
    # which is nonnegative for d>=9, i.e. t>=45. The loop below
    # is an audit of the formula; its proof is the displayed finite sum.
    for d in range(7, 40):
        for e in range(d + 1):
            assert q(d * (d + 1) // 2 + e) == 7 * d - 58 + p(e)
    C = 224 + 11
    assert C == 235

    # The finitely many early AX-prefix cases excluded by 9*k+10-C>=0.
    ax_balance, ax_checks = 0, []
    for k in range(26):
        r = f(f(k))
        assert ax_balance >= 0
        inside = ax_balance + 10 + (m[r - 1] if r else 0)
        assert inside >= 0
        after = ax_balance + 10 + (b[r - 1] if r else 0)
        ax_checks.append(dict(k=k, remainder=r, before=ax_balance,
                              minimum_after_AX=inside, after=after))
        ax_balance = after
    assert 10 * 26 - C >= 0
    assert 9 * 26 + 10 - C >= 0
    assert 7 * 36 - 17 - C == 0

    # Independent reconstruction of the two truth heads over the dirty tail.
    assert pair(0, pair(0, 1)) == 5
    assert unpair(5) == (0, 2) and unpair(2) == (0, 1)
    from_one_total, from_one_min = 0, 0
    for n in range(1, 666):
        from_one_min = min(from_one_min, from_one_total + m[n])
        from_one_total += b[n]
    assert from_one_min == -2
    result = dict(
        status='FINITE_PREMISES_OF_DEBT_TWO_INDUCTION_PASS',
        scope='Checks the finite premises of the separate all-natural Cantor-diagonal proof; no binary execution or theoremhood oracle.',
        command_order=['NIP', 'DROP', 'MP'],
        candidate_range=[0, 665], complete_base_diagonals=[0, 35],
        conservative_balance_from_zero=-3,
        conservative_balance_from_one=-2,
        first_minimum_candidate=first_minimum,
        minimum_complete_balance_after_candidate_6=min(cumulative[6:]),
        small_prefix_lower_bounds=small_p,
        q_values_below_45=q45, q_minimum=-11,
        negative_q_sum=-224, double_unpair_prefix_lower_bound=-C,
        AX_small_cases=ax_checks,
        induction_first_diagonal=36,
        tail_bound='10*(s-2)-235-(3*s-3)=7*s-252 >= 0 for s>=36',
        seed=dict(next_candidate=1, current=0, stack=5, cache=0,
                  truth_prefix=[0, 0], protected_tail=1),
        early_candidates=early,
        script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    text = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text)
    print(json.dumps({key: value for key, value in result.items()
                      if key not in ('AX_small_cases', 'early_candidates', 'q_values_below_45')}, indent=2))


if __name__ == '__main__':
    main()
