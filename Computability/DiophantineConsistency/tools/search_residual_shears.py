#!/usr/bin/env python3
"""Exact bounded residual-shear search in weighted polynomial abbreviations."""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
DESTINATION = ROOT / 'Computability/DiophantineConsistency/circuits/residual_shear_search.json'
NAMES = ['X', 'Y', 'k', 'eta', 'tau', 'i', 'f', 'T', 'R', 'y']
WEIGHTS = [2, 4, 1, 1, 1, 1, 1, 1, 4, 1]
ZERO = (0,) * len(NAMES)


def constant(n): return {ZERO: n} if n else {}
def variable(name):
    e = list(ZERO)
    e[NAMES.index(name)] = 1
    return {tuple(e): 1}
def add(p, q, sign=1):
    r = dict(p)
    for e, c in q.items():
        r[e] = r.get(e, 0) + sign * c
        if not r[e]: del r[e]
    return r
def sub(p, q): return add(p, q, -1)
def mul(p, q):
    r = {}
    for e, c in p.items():
        for f, d in q.items():
            g = tuple(a + b for a, b in zip(e, f))
            r[g] = r.get(g, 0) + c * d
    return {e: c for e, c in r.items() if c}
def scale(n, p): return {e: n * c for e, c in p.items() if n * c}
def power(p, n):
    r = constant(1)
    for _ in range(n): r = mul(r, p)
    return r
def degree(p):
    return max((sum(a * b for a, b in zip(e, WEIGHTS)) for e in p), default=0)
def top(p):
    d = degree(p)
    return {e: c for e, c in p.items() if sum(a * b for a, b in zip(e, WEIGHTS)) == d}


def main():
    X, Y, k, eta, tau, i, f, T, R, y = map(variable, NAMES)
    one = constant(1)
    b = mul(k, Y)
    c = add(b, eta)
    a = add(mul(X, Y), Y)
    delta = add(add(power(a, 2), scale(4, a)), constant(3))
    n = mul(X, power(Y, 2))
    r0 = sub(sub(power(tau, 2), mul(mul(n, add(n, one)), power(k, 2))), one)
    rs = sub(sub(power(f, 2), one), mul(delta, mul(power(i, 2), power(c, 4))))
    v = sub(mul(c, sub(mul(T, f), one)), mul(R, power(f, 2)))
    ra = sub(add(mul(mul(delta, sub(power(f, 2), one)),
                      sub(power(v, 2), power(y, 2))), power(y, 2)), one)
    strong_counts = {}
    strong_records = []
    for A in range(-2, 3):
        for B in range(-4, 5):
            for C in range(-4, 5):
                coefficient = mul(power(i, 2), add(add(scale(A, power(b, 2)),
                    scale(B, mul(b, eta))), scale(C, power(eta, 2))))
                d = degree(sub(rs, mul(coefficient, r0)))
                strong_counts[str(d)] = strong_counts.get(str(d), 0) + 1
                if A == 1 and d != 32: raise ValueError('unexpected strong-family degree')
                if A != 1 and d != 34: raise ValueError('unexpected uncancelled degree')
                if (A, B, C) == (1, 2, 1):
                    strong_records.append({'A': A, 'B': B, 'C': C, 'degree': d})
    corrected_strong = sub(rs, mul(mul(power(i, 2), power(c, 2)), r0))
    expected_strong_top = scale(-2, mul(mul(mul(power(i, 2), power(k, 4)), X), power(Y, 6)))
    assert top(corrected_strong) == expected_strong_top
    auxiliary_counts = {}
    for A in range(-2, 3):
        for B in range(-4, 5):
            coefficient = mul(power(mul(T, f), 2), add(scale(A, power(f, 2)), constant(B)))
            d = degree(add(ra, mul(coefficient, r0)))
            auxiliary_counts[str(d)] = auxiliary_counts.get(str(d), 0) + 1
            assert d == (27 if A == 1 else 28)
    auxiliary_coefficient = mul(power(mul(T, f), 2), sub(power(f, 2), one))
    corrected_auxiliary = add(ra, mul(auxiliary_coefficient, r0))
    expected_auxiliary_top = scale(-2, mul(mul(mul(mul(mul(power(X, 2), k),
        power(Y, 3)), T), R), power(f, 5)))
    assert top(corrected_auxiliary) == expected_auxiliary_top
    result = {
        'variables': NAMES, 'weights': dict(zip(NAMES, WEIGHTS)),
        'original_degrees': {'first_residual': degree(r0), 'strong_residual': degree(rs),
                             'auxiliary_residual': degree(ra)},
        'strong_family': 'Rs-i^2*(A*(k*Y)^2+B*k*Y*eta+C*eta^2)*R0',
        'strong_ranges': {'A': [-2, 2], 'B': [-4, 4], 'C': [-4, 4]},
        'strong_cases': 405, 'strong_degree_distribution': strong_counts,
        'p76_member': strong_records[0],
        'p76_strong_leading_form': '-2*i^2*k^4*X*Y^6',
        'auxiliary_family': 'Ra+(T*f)^2*(A*f^2+B)*R0',
        'auxiliary_ranges': {'A': [-2, 2], 'B': [-4, 4]},
        'auxiliary_cases': 45, 'auxiliary_degree_distribution': auxiliary_counts,
        'auxiliary_example': {'A': 1, 'B': -1, 'degree': degree(corrected_auxiliary),
            'extra_literal_gates': 4, 'leading_form': '-2*X^2*k*Y^3*T*R*f^5'},
        'scope': 'Exact finite symbolic family search; not a global operation or degree minimum.'
    }
    DESTINATION.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))

if __name__ == '__main__': main()
