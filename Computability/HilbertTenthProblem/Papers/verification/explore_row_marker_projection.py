#!/usr/bin/env python3
"""Exact conditional marker projection; this is not a universal certificate."""
from itertools import product
from pathlib import Path
import json


def boolean(n):
    if n < 0:
        return False
    while n:
        n, d = divmod(n, 3)
        if d == 2:
            return False
    return True


def words(length):
    return [sum(v*3**i for i, v in enumerate(ds))
            for ds in product((0, 1), repeat=length)]


def rows(n, R, t):
    result = []
    for _ in range(t):
        n, r = divmod(n, R)
        result.append(r)
    assert n == 0
    return result


def exact_form(Q, S, M, m, t):
    R = 3**m
    for q, s, marker in zip(rows(Q, R, t), rows(S, R, t), rows(M, R, t)):
        if s == 0:
            assert q == marker == 0
        else:
            assert s == 1
            assert any(marker == 3**p and q == (3**p-1)//2 for p in range(m))


def verify_guard_depth():
    candidates = accepted = converse = dag_cases = 0
    for m in range(1, 5):
        for t in (1, 2):
            R = 3**m
            scale = R**t
            H = (scale-1)//(R-1)
            heads = [sum(v*R**j for j, v in enumerate(ds))
                     for ds in product((0, 1), repeat=t)]
            for b in range(m):
                A, C = 3**b, 3**(m-b)
                assert C >= 3 and C*A == R
                for Q in words(m*t):
                    for S in heads:
                        candidates += 1
                        M = 2*Q+S
                        Qguard = Q+A*H
                        if not (M < scale and Qguard < scale
                                and boolean(M) and boolean(Qguard)):
                            continue
                        exact_form(Q, S, M, m, t)
                        for row_q, row_s, row_m in zip(
                                rows(Q, R, t), rows(S, R, t), rows(M, R, t)):
                            assert row_q <= (R-1)//2-A
                            assert 0 <= 2*row_q+row_s <= R-2*A < R
                            assert row_m <= A
                        accepted += 1
                for positions in product(range(-1, b+1), repeat=t):
                    S = sum(int(p >= 0)*R**j for j, p in enumerate(positions))
                    Q = sum(((3**p-1)//2 if p >= 0 else 0)*R**j
                            for j, p in enumerate(positions))
                    M = sum((3**p if p >= 0 else 0)*R**j
                            for j, p in enumerate(positions))
                    reg = dict(A=A, H=H, Q=Q, S=S, Sbar=H-S)
                    dag = [('radix', '*', C, 'A'), ('guard', '*', 'A', 'H'),
                           ('Qguard', '+', 'Q', 'guard'),
                           ('headsum', '+', 'S', 'Sbar'),
                           ('twiceQ', '*', 2, 'Q'),
                           ('projected', '+', 'twiceQ', 'S')]
                    assert sum(op == '*' for _, op, _, _ in dag) == 3
                    assert sum(op == '+' for _, op, _, _ in dag) == 3
                    for name, op, left, right in dag:
                        x = reg[left] if isinstance(left, str) else left
                        y = reg[right] if isinstance(right, str) else right
                        reg[name] = x*y if op == '*' else x+y
                    assert reg['radix'] == R and reg['headsum'] == H
                    assert reg['projected'] == M
                    assert all(0 <= v < scale and boolean(v)
                               for v in (Q, S, H-S, M, reg['Qguard']))
                    converse += 1
                    dag_cases += 1
    assert accepted == converse
    return dict(exhaustive_candidates=candidates, accepted_candidates=accepted,
                converse_choices=converse, dag_cases=dag_cases,
                component_total=6, masked_words=5,
                scope='Every fixed guard depth, with exact bound M_row<=R/C and the paid quotient C*A=R. Conditional nonnegative component only.')


def verify():
    candidates = accepted = converse = 0
    # Every Boolean Q and every typed selector is considered; M is
    # determined, so rejecting a non-Boolean/out-of-range M is exhaustive.
    dimensions = [(m, 1) for m in range(1, 9)] + [(2, 2), (2, 3), (3, 2), (3, 3)]
    for m, t in dimensions:
        R = 3**m
        scale = R**t
        H = (scale-1)//(R-1)
        top = (R//3)*H
        heads = [sum(v*R**j for j, v in enumerate(ds))
                 for ds in product((0, 1), repeat=t)]
        for Q in words(m*t):
            for S in heads:
                candidates += 1
                M = 2*Q+S
                if M >= scale or not boolean(M) or not boolean(Q+top):
                    continue
                assert boolean(H-S) and Q+top < scale
                exact_form(Q, S, M, m, t)
                accepted += 1
        for positions in product(range(-1, m), repeat=t):
            S = sum(int(p >= 0)*R**j for j, p in enumerate(positions))
            Q = sum(((3**p-1)//2 if p >= 0 else 0)*R**j
                    for j, p in enumerate(positions))
            M = sum((3**p if p >= 0 else 0)*R**j
                    for j, p in enumerate(positions))
            assert 2*Q+S == M
            assert all(0 <= x < scale and boolean(x)
                       for x in (Q, S, H-S, M, Q+top))
            exact_form(Q, S, M, m, t)
            converse += 1
    assert accepted == converse

    # Each omitted premise has a concrete example, not a failed search.
    R, H, top = 9, 10, 30
    Q, S, M = 4, 1, 9
    assert all(boolean(x) for x in (Q, S, H-S, M)) and 2*Q+S == M
    assert not boolean(Q+top)
    Q, S, M = 6, 1, 13
    assert 2*Q+S == M and Q+top == 36
    assert all(boolean(x) for x in (S, H-S, M, Q+top)) and not boolean(Q)
    assert M % R == 4  # Two first-row markers.
    assert 2*0+3 == 3  # Untyped selector away from the row head.

    dag = [('threeA', '*', 3, 'A'), ('top', '*', 'A', 'H'),
           ('Qtop', '+', 'Q', 'top'), ('headsum', '+', 'S', 'Sbar'),
           ('twiceQ', '*', 2, 'Q'), ('projected', '+', 'twiceQ', 'S')]
    # Evaluate the actual six-operation DAG on all one-row converse cases.
    dag_cases = 0
    for m in range(1, 9):
        for p in range(-1, m):
            S = int(p >= 0)
            Q = (3**p-1)//2 if p >= 0 else 0
            M = 3**p if p >= 0 else 0
            reg = dict(A=3**(m-1), H=1, Q=Q, S=S, Sbar=1-S)
            for name, op, left, right in dag:
                a = reg[left] if isinstance(left, str) else left
                b = reg[right] if isinstance(right, str) else right
                assert name not in reg
                reg[name] = a*b if op == '*' else a+b
            assert reg['threeA'] == 3**m and reg['headsum'] == 1
            assert reg['projected'] == M and boolean(reg['Qtop'])
            dag_cases += 1
    return dict(status='PASS_CONDITIONAL_ROW_MARKER_PROJECTION',
                dimensions=dimensions, exhaustive_candidates=candidates,
                accepted_candidates=accepted, converse_choices=converse,
                omission_examples=3, dag=dag, dag_cases=dag_cases,
                component_multiplications=3, component_additions=3,
                component_total=6, already_available_quotient_total=5,
                masked_words=5,
                arbitrary_fixed_guard_depth=verify_guard_depth(),
                scope='Nonnegative conditional component with supplied radix geometry and Boolean words/ranges. Neither mask realization nor input, alignment, halting or positive-witness adapters are counted. No new universal operation bound.')


if __name__ == '__main__':
    receipt = verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(receipt, indent=2)+'\n', encoding='utf-8')
    print(receipt['status'])
    print({k:v for k,v in receipt.items() if k != 'dag'})
