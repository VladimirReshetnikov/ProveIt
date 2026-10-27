#!/usr/bin/env python3
"""Independent exact audit of the joint crossing-block factorization.

Uses only the Python standard library. Run normally or with python -O;
all checks use explicit exceptions and remain active in either mode.
This is a local algebraic verifier, not a SAT solver or an end-to-end
verification of the ETH manuscript. By default, writes a JSON record
into the package results directory.
"""
import argparse
from fractions import Fraction
from itertools import combinations, permutations
from math import factorial
import json
from pathlib import Path
CHECK_COUNT = 0

def check(condition, detail):
    global CHECK_COUNT
    if not condition:
        raise ArithmeticError(f'Independent Cauchy audit failed: {detail}')
    CHECK_COUNT += 1

def v2int(n):
    if n == 0:
        return 10 ** 9
    n = abs(n)
    return (n & -n).bit_length() - 1

def v2rat(x):
    return v2int(x.numerator) - v2int(x.denominator) if x else 10 ** 9

def points(a, i, orientation=0):
    R = 1 << i
    return [orientation * R + j % R + 2 * R * (j // R) for j in range(1 << a - 1)]

def exponent(b, i):
    q = b // (1 << i)
    return q + v2int(factorial(q))

def rational_factors(a, i, T, orientation=0):
    ss = points(a, i, orientation)
    n = len(ss)
    LL = [[Fraction(0) for _ in range(n)] for _ in range(n)]
    UU = [[Fraction(0) for _ in range(n)] for _ in range(n)]
    pp = [Fraction(1) for _ in ss]
    qq = [Fraction(1) for _ in ss]
    for b, pivot in enumerate(ss):
        ee = exponent(b, i)
        for j, x in enumerate(ss):
            check(v2rat(pp[j]) >= ee, 'v2rat(pp[j]) >= ee')
            check(v2rat(qq[j]) >= ee, 'v2rat(qq[j]) >= ee')
            LL[j][b] = T * pp[j] / ((T + x - pivot) * (1 << ee))
            UU[b][j] = T * qq[j] / ((T + pivot - x) * (1 << ee))
            check(v2rat(LL[j][b]) >= 0, 'v2rat(LL[j][b]) >= 0')
            check(v2rat(UU[b][j]) >= 0, 'v2rat(UU[b][j]) >= 0')
            if j < b:
                check(LL[j][b] == UU[b][j] == 0, 'LL[j][b] == UU[b][j] == 0')
        check(v2rat(pp[b]) == v2rat(qq[b]) == ee, 'v2rat(pp[b]) == v2rat(qq[b]) == ee')
        check(v2rat(LL[b][b]) == v2rat(UU[b][b]) == 0, 'v2rat(LL[b][b]) == v2rat(UU[b][b]) == 0')
        for j, x in enumerate(ss):
            pp[j] *= Fraction(x - pivot, 1) / (T + x - pivot)
            qq[j] *= Fraction(pivot - x, 1) / (T + pivot - x)
    for xj, x in enumerate(ss):
        for yj, y in enumerate(ss):
            found = sum((LL[xj][b] * (1 << 2 * exponent(b, i)) * UU[b][yj] for b in range(n)))
            check(found == T / (T + x - y), (a, i, T, x, y))
    return (ss, LL, UU)

def determinant(mat):
    n = len(mat)
    result = Fraction(0)
    for perm in permutations(range(n)):
        parity = sum((perm[i] > perm[j] for i in range(n) for j in range(i + 1, n)))
        term = Fraction((-1) ** parity)
        for i, j in enumerate(perm):
            term *= mat[i][j]
        result += term
    return result

def rational_checks():
    count = 0
    entries = 0
    checks = 0
    for a in range(1, 6):
        for i in range(a):
            R = 1 << i
            for sign in (-1, 1):
                t = sign * R
                for zeta in (Fraction(0), Fraction(1, 3), Fraction(-2, 5)):
                    T = Fraction(t) + (1 << a + 1) * zeta
                    check(v2rat(T) == i, 'v2rat(T) == i')
                    for orientation in (0, 1):
                        ss, _, _ = rational_factors(a, i, T, orientation)
                        count += 1
                        entries += len(ss) ** 2
                        if len(ss) <= 4 and orientation == 0 and (zeta == Fraction(1, 3)):
                            for rank in range(1, len(ss) + 1):
                                expected = sum((2 * exponent(b, i) for b in range(rank)))
                                minimum = 10 ** 9
                                for rows in combinations(range(len(ss)), rank):
                                    for cols in combinations(range(len(ss)), rank):
                                        mat = [[T / (T + ss[x] - ss[y]) for y in cols] for x in rows]
                                        value = v2rat(determinant(mat))
                                        check(value >= expected, 'value >= expected')
                                        minimum = min(minimum, value)
                                        checks += 1
                                check(minimum == expected, 'minimum == expected')
    return {'rational_factorizations': count, 'matrix_entries': entries, 'exhaustive_minor_checks': checks}

class F4Lift:
    """(Z/2^p)[U]/(U^2+U+1), with unit inverse by the conjugate norm."""

    def __init__(self, p):
        self.mod = 1 << p
        self.one = (1, 0)
        self.zero = (0, 0)

    def add(self, x, y):
        return ((x[0] + y[0]) % self.mod, (x[1] + y[1]) % self.mod)

    def mul(self, x, y):
        a, b = x
        c, d = y
        return ((a * c - b * d) % self.mod, (a * d + b * c - b * d) % self.mod)

    def scale(self, x, n):
        return (x[0] * n % self.mod, x[1] * n % self.mod)

    def inv(self, x):
        a, b = x
        norm = (a * a - a * b + b * b) % self.mod
        check(norm & 1, 'norm & 1')
        nn = pow(norm, -1, self.mod)
        return ((a - b) * nn % self.mod, -b * nn % self.mod)

    def is_unit(self, x):
        return bool((x[0] | x[1]) & 1)

def extension_factors(a, i, t, zeta, precision):
    rr = F4Lift(precision)
    ss = points(a, i)
    n = len(ss)
    alpha = 1 << a + 1
    rawT = (t + alpha * zeta[0], alpha * zeta[1])
    unitT = (rawT[0] // (1 << i), rawT[1] // (1 << i))

    def den_unit(diff):
        vv = v2int(t + diff)
        check(vv <= i, 'vv <= i')
        return (vv, ((rawT[0] + diff) // (1 << vv), rawT[1] // (1 << vv)))

    def normalized_product(x, b, reverse):
        out = rr.one
        power = -exponent(b, i)
        for pivot in ss[:b]:
            diff = pivot - x if reverse else x - pivot
            if diff == 0:
                return rr.zero
            vn = v2int(diff)
            vd, ud = den_unit(diff)
            power += vn - vd
            out = rr.mul(out, rr.scale(rr.inv(ud), diff // (1 << vn)))
        check(power >= 0, 'power >= 0')
        return rr.scale(out, 1 << power)

    def ratio_T(diff):
        vd, ud = den_unit(diff)
        check(i >= vd, 'i >= vd')
        return rr.scale(rr.mul(unitT, rr.inv(ud)), 1 << i - vd)
    LL = [[rr.zero for _ in ss] for _ in ss]
    UU = [[rr.zero for _ in ss] for _ in ss]
    for b, pivot in enumerate(ss):
        for j, x in enumerate(ss):
            LL[j][b] = rr.mul(ratio_T(x - pivot), normalized_product(x, b, False))
            UU[b][j] = rr.mul(ratio_T(pivot - x), normalized_product(x, b, True))
            if j < b:
                check(LL[j][b] == UU[b][j] == rr.zero, 'LL[j][b] == UU[b][j] == rr.zero')
        check(rr.is_unit(LL[b][b]) and rr.is_unit(UU[b][b]), 'rr.is_unit(LL[b][b]) and rr.is_unit(UU[b][b])')
    for j, x in enumerate(ss):
        for k, y in enumerate(ss):
            out = rr.zero
            for b in range(n):
                term = rr.scale(rr.mul(LL[j][b], UU[b][k]), 1 << 2 * exponent(b, i))
                out = rr.add(out, term)
            check(out == ratio_T(x - y), (a, i, t, zeta, precision, j, k))
    return n * n

def extension_checks():
    count = 0
    entries = 0
    for a in range(1, 6):
        for i in range(a):
            for sign in (-1, 1):
                for zeta in ((0, 1), (1, 1), (2, 2)):
                    for precision in (7, 19):
                        entries += extension_factors(a, i, sign * (1 << i), zeta, precision)
                        count += 1
    return {'unramified_extension_factorizations': count, 'unramified_matrix_entries': entries, 'unramified_moduli_bits': [7, 19], 'unramified_polynomial': 'U^2+U+1'}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path(__file__).resolve().parents[1] / 'results' / 'joint_cauchy_independent_validation.json')
    args = parser.parse_args()
    result = {'status': 'PASS', **rational_checks(), **extension_checks(), 'checked_conditions': CHECK_COUNT, 'optimized_python': not __debug__, 'scope': 'Independent finite local algebra checks; not an end-to-end SAT solver.'}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(result, indent=2))
if __name__ == '__main__':
    main()
