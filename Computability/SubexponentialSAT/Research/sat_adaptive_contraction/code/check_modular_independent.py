#!/usr/bin/env python3
"""Independent lifted-polynomial oracle; no production implementation changes.

Evaluates W directly as product(T-q), omitting q=y-x, modulo
2^(p+v2(C'(0))). The known scalar denominator valuation is then removed.
This uses neither the modular kernel's pre-factor nor its feature recurrence.
"""
from pathlib import Path
import hashlib
import json
import random
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from modular_cauchy import ModularCauchy


def v2(n):
    n = abs(n)
    if n == 0:
        raise ArithmeticError('zero in scalar valuation')
    return (n & -n).bit_length()-1


def multiply(x, y, mask):
    a, b = x
    c, d = y
    return ((a*c-b*d) & mask, (a*d+b*c-b*d) & mask)


def direct_polynomial(a, i, t, zeta, p, row, col):
    L, R = 1 << a, 1 << i
    x = row % R + 2*R*(row//R)
    y = col % R + 2*R*(col//R)
    den_v = sum(v2(q) for q in range(-L, L) if q)
    mask = (1 << (p+den_v))-1
    alpha = 1 << (a+1)
    T = (t+alpha*zeta[0], alpha*zeta[1])
    product = (1, 0)
    denominator_unit = 1
    for q in range(-L, L):
        if q != y-x:
            product = multiply(product, (T[0]-q, T[1]), mask)
        if q:
            denominator_unit *= (-q) >> v2(q)
            denominator_unit &= mask
    inverse = pow(denominator_unit, -1, mask+1)
    lifted = tuple((c*inverse) & mask for c in product)
    if any(c % (1 << den_v) for c in lifted):
        raise ArithmeticError('direct polynomial integrality failed')
    return tuple(c >> den_v for c in lifted)


def reconstruct(target, source, row, col, p):
    mask = (1 << p)-1
    total = (0, 0)
    for b in range(len(target)):
        value = multiply(target[b][row], source[b][col], mask)
        total = tuple((x+y) & mask for x, y in zip(total, value))
    return total


def main():
    rng = random.Random(202610271)
    cases, entries, full_tables, direct_entries = 0, 0, 0, 0
    digest = hashlib.sha256()
    for a in range(1, 9):
        for i in sorted({0, a//2, a-1}):
            if i >= a:
                continue
            L, n = 1 << a, 1 << (a-1)
            valid_t = [t for t in range(-L+1, L) if t and v2(t) == i]
            for rep in range(3):
                t = rng.choice(valid_t)
                p = rng.choice((1, 2, 3, 9, 17, 32, 65, 129))
                zeta = rng.choice(((0, 0), (0, 1), (-7, 4), (2, 2),
                                   ((1 << 60)+3, -(1 << 59)+2)))
                kernel = ModularCauchy(a, i, t, zeta, p)
                target, source = kernel.feature_tables()
                if a <= 4:
                    from reference_joint_cauchy import JointCauchyKernel, Quadratic, residue
                    exact = JointCauchyKernel(a, i, t, Quadratic(*zeta))
                    et, es = exact.feature_tables()
                    mt, ms = kernel.feature_tables(truncate=False)
                    if len(mt) != n or len(ms) != n:
                        raise ArithmeticError('full table has wrong mode count')
                    for mode in range(n):
                        for index in range(n):
                            if mt[mode][index] != residue(et[mode][index], p):
                                raise ArithmeticError('full target mismatch')
                            if ms[mode][index] != residue(es[mode][index], p):
                                raise ArithmeticError('full source mismatch')
                    full_tables += 1
                sample = {(0, 0), (0, n-1), (n-1, 0), (n-1, n-1)}
                sample.update((rng.randrange(n), rng.randrange(n)) for _ in range(5))
                for row, col in sorted(sample):
                    actual = reconstruct(target, source, row, col, p)
                    expected = direct_polynomial(a, i, t, zeta, p, row, col)
                    if actual != expected:
                        raise ArithmeticError((a, i, t, zeta, p, row, col, actual, expected))
                    if kernel.direct_entry(row, col) != expected:
                        raise ArithmeticError('public direct_entry differs from polynomial oracle')
                    direct_entries += 1
                    entries += 1
                    digest.update(repr((a, i, t, zeta, p, row, col, actual)).encode())
                cases += 1
    result = {'status': 'PASS', 'cases': cases, 'matrix_entries': entries,
              'full_exact_tables': full_tables, 'public_direct_entries': direct_entries,
              'max_a': 8, 'max_N': 128, 'precision_choices': [1,2,3,9,17,32,65,129],
              'includes_zero_nonunit_and_large_signed_extension_inputs': True,
              'digest': digest.hexdigest(), 'optimized_python': not __debug__,
              'oracle': 'Independent high-precision cancelled polynomial, followed by exact scalar valuation division.',
              'scope': 'Local kernel only; no SAT benchmark or complete contraction certificate.'}
    path = Path(__file__).resolve().parents[1] / 'results' / ('independent_modular_validation' + ('_optimized' if not __debug__ else '') + '.json')
    path.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
