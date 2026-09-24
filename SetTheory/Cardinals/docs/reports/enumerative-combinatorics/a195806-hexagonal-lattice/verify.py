#!/usr/bin/env python3
"""Exact certificates and independent checks for the A195806 manuscript.

Python 3.10+, standard library only. No network access or third-party packages.
Run: python3 verify.py --output-dir data
Assertions below are explicit exceptions, and remain active under python -O.
Finite enumeration tests complement (but do not replace) the manuscript's proof.
The three polynomial certificates establish identities for all coefficients.
"""
from __future__ import annotations

import argparse
import csv
import itertools
import json
import platform
import time
from fractions import Fraction
from pathlib import Path
from typing import Iterable, Sequence

Poly = list[int]  # Coefficients in ascending order.
P: Poly = [1, 13, 59, 212, 471, 753, 882, 753, 471, 212, 59, 13, 1]
Q: Poly = [1, -3, 2, -1, 6, -5, -3, 0, 3, 5, -6, 1, -2, 3, -1]
RESIDUES: list[Poly] = [
    [1, 25, 158, 650, 2275, 4680, 4680],
    [16, 198, 1133, 3900, 8125, 9360, 4680],
    [105, 1087, 4922, 12350, 17875, 14040, 4680],
    [496, 4148, 14783, 28600, 31525, 18720, 4680],
    [1759, 12121, 35258, 55250, 49075, 23400, 4680],
    [5052, 29474, 72197, 94900, 70525, 28080, 4680],
]
OEIS_FIRST = [16, 105, 496, 1759, 5052, 12469, 27412, 55059, 102952,
              181543, 304908, 491563, 765184, 1155567, 1699684, 2442553,
              3438468, 4752283, 6460432, 8652429, 11432392, 14920189,
              19253232, 24588229, 31102456, 38995845, 48492976, 59844451,
              73329300]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def trim(a: Sequence[int]) -> Poly:
    b = list(a) or [0]
    while len(b) > 1 and b[-1] == 0:
        b.pop()
    return b


def add(*args: Sequence[int]) -> Poly:
    out = [0] * max((len(a) for a in args), default=1)
    for a in args:
        for j, c in enumerate(a):
            out[j] += c
    return trim(out)


def scale(a: Sequence[int], c: int) -> Poly:
    return trim([c * x for x in a])


def mul(a: Sequence[int], b: Sequence[int]) -> Poly:
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return trim(out)


def power(a: Sequence[int], n: int) -> Poly:
    if n < 0:
        raise ValueError('Polynomial exponent must be nonnegative.')
    out = [1]
    b = list(a)
    while n:
        if n & 1:
            out = mul(out, b)
        b = mul(b, b)
        n //= 2
    return out


def deriv(a: Sequence[int]) -> Poly:
    return trim([j * a[j] for j in range(1, len(a))])


def compose(a: Sequence[int], b: Sequence[int]) -> Poly:
    out = [0]
    for c in reversed(a):
        out = add(mul(out, b), [c])
    return out


def evaluate(a: Sequence[int], x: int) -> int:
    out = 0
    for c in reversed(a):
        out = out * x + c
    return out


def monomial(n: int, c: int = 1) -> Poly:
    return [0] * n + [c]


def remainder_monic(a: Sequence[int], b: Sequence[int]) -> Poly:
    if b[-1] != 1:
        raise ValueError('Divisor must be monic.')
    r = trim(a)
    while len(r) >= len(b) and r != [0]:
        d, c = len(r) - len(b), r[-1]
        r = add(r, scale([0] * d + list(b), -c))
    return r


def nonnegative_integer(n: int) -> None:
    if isinstance(n, bool) or not isinstance(n, int) or n < 0:
        raise ValueError('The array bound must be a nonnegative integer.')


def quasipolynomial(n: int) -> int:
    """Polynomial continuation for every integer n; counts arrays for n >= 0."""
    if isinstance(n, bool) or not isinstance(n, int):
        raise ValueError('The index must be an integer.')
    k, r = divmod(n, 6)
    return evaluate(RESIDUES[r], k)


def multiplicity(p: int, q: int) -> int:
    return 1 if p == q == 0 else 6 if p == 0 or q == 0 else 12


def chamber_count(n: int) -> int:
    nonnegative_integer(n)
    total = 0
    for p in range(n // 2 + 1):
        for q in range((n - 2 * p) // 3 + 1):
            r = n - 2 * p - 3 * q
            total += multiplicity(p, q) * (r + 1) ** 2 * (r + p + q + 1) ** 2
    return total


def h1(x: int, y: int) -> int:
    return max(abs(x), abs(y), abs(x - y))


def h2(x: int, y: int) -> int:
    return max(abs(x + y), abs(2 * x - y), abs(x - 2 * y))


def norm_count(n: int, m: int | None = None) -> int:
    nonnegative_integer(n)
    if m is None:
        m = n
    nonnegative_integer(m)
    # A nonzero summand has h1 <= n, hence |x|, |y| <= n.
    return sum(max(0, n + 1 - h1(x, y)) ** 2 *
               max(0, m + 1 - h2(x, y)) ** 2
               for x in range(-n, n + 1) for y in range(-n, n + 1))


def mixed_count(n: int, m: int) -> int:
    nonnegative_integer(n)
    nonnegative_integer(m)
    total = 0
    for p in range(min(n, m // 2) + 1):
        for q in range(min((n - p) // 2, (m - 2 * p) // 3) + 1):
            total += (multiplicity(p, q) * (n + 1 - p - 2 * q) ** 2 *
                      (m + 1 - 2 * p - 3 * q) ** 2)
    return total


def parametrization(x: int, y: int, alpha: int, beta: int,
                    gamma: int, delta: int) -> tuple[int, ...]:
    """Return the twelve entries a,b,c,d,e,f,g,h,i,j,k,l."""
    return (beta + y, alpha + x - y, delta + 2 * x - y, gamma,
            delta + x + y, alpha, gamma + x + y, gamma + 2 * x - y,
            beta, beta + x, delta, alpha + x)


POSITIONS = [(r, c) for r in range(5) for c in range(r + 1)]
CORNERS = {(0, 0), (4, 0), (4, 4)}
VARIABLES = [p for p in POSITIONS if p not in CORNERS]
# Construct the line constraints independently from triangular-grid coordinates.
LINE_PAIRS: list[tuple[tuple[int, ...], tuple[int, ...]]] = []
for length in range(2, 6):
    row = [(length - 1, c) for c in range(length)]
    col = [(r, 5 - length) for r in range(5 - length, 5)]
    diag = [(r, r - (5 - length)) for r in range(5 - length, 5)]
    indices = [tuple(VARIABLES.index(p) for p in line if p not in CORNERS)
               for line in (row, col, diag)]
    LINE_PAIRS.extend([(indices[0], indices[1]), (indices[0], indices[2])])


def grid_valid(entries: Sequence[int]) -> bool:
    return all(sum(entries[j] for j in left) == sum(entries[j] for j in right)
               for left, right in LINE_PAIRS)


def inverse(entries: Sequence[int]) -> tuple[int, ...]:
    a, b, c, d, e, f, g, h, i, j, k, ell = entries
    return (j - i, a - i, f, i, d, k)


def brute_count(n: int) -> tuple[int, int]:
    nonnegative_integer(n)
    count = 0
    for entries in itertools.product(range(n + 1), repeat=12):
        if grid_valid(entries):
            count += 1
            require(parametrization(*inverse(entries)) == entries,
                    'Parametrization inverse failed on an original-grid solution.')
    return count, (n + 1) ** 12


def rotation(x: int, y: int) -> tuple[int, int]:
    return x - y, x


def reflection(x: int, y: int) -> tuple[int, int]:
    return x, x - y


def orbit(x: int, y: int) -> set[tuple[int, int]]:
    out: set[tuple[int, int]] = set()
    for _ in range(6):
        out.update(((x, y), reflection(x, y)))
        x, y = rotation(x, y)
    return out


def rational_coefficients(nmax: int) -> list[int]:
    out = []
    for n in range(nmax + 1):
        pn = P[n] if n < len(P) else 0
        out.append(pn - sum(Q[j] * out[n - j]
                            for j in range(1, min(n, len(Q) - 1) + 1)))
    return out


def centered_formula(n: int) -> Fraction:
    N = n + 1
    mean = (Fraction(65, 648) * N ** 6 + Fraction(325, 1296) * N ** 4 +
            Fraction(439, 324) * N ** 2 - Fraction(2521, 7776))
    terms = [Fraction(2 * (3 * N * N - 24 * N - 14), 243),
             Fraction(2 * (3 * N * N + 24 * N - 14), 243),
             Fraction(-4 * (3 * N * N - 14), 243)]
    parity = 1 if n % 2 == 0 else -1
    return mean - Fraction(3 * parity, 32) + terms[n % 3]


def polynomial_certificates() -> dict[str, int | list[int]]:
    z, U, V = [0, 1], monomial(2), monomial(3)
    omz, omU, omV = [1, -1], add([1], scale(U, -1)), add([1], scale(V, -1))
    M0 = add([1], scale(U, 5), scale(V, 5), mul(U, V))
    M1 = scale(mul(add(U, V), add([1], scale(mul(U, V), -1))), 6)
    inner = add([1], U, V, scale(mul(U, V), -6), mul(power(U, 2), V),
                mul(U, power(V, 2)), mul(power(U, 2), power(V, 2)))
    M2 = scale(mul(add(U, V), inner), 6)
    lhs = add(mul(mul(mul([1, 11, 11, 1], M0), power(omU, 2)), power(omV, 2)),
              scale(mul(mul(mul(mul([1, 4, 1], omz), M1), omU), omV), 2),
              mul(mul([1, 1], power(omz, 2)), M2))
    rhs = mul(mul(power(omz, 2), power(omU, 2)), P)
    require(lhs == rhs, 'Generating-function polynomial certificate failed.')
    Qfactor = mul(mul(power(omz, 7), [1, 1]), power([1, 1, 1], 3))
    require(Qfactor == Q, 'Denominator factorization failed.')

    # T_d/(1-t)^(d+1) = sum_{k>=0} k^d t^k, with 0^0=1.
    T: list[Poly] = [[1]]
    for d in range(6):
        T.append(mul(z, add(mul(omz, deriv(T[-1])), scale(T[-1], d + 1))))
    W = monomial(6)
    omW = add([1], scale(W, -1))
    H = [0]
    for r, coeffs in enumerate(RESIDUES):
        for d, c in enumerate(coeffs):
            part = mul(mul(monomial(r), compose(T[d], W)), power(omW, 6 - d))
            H = add(H, scale(part, c))
    left_residue = mul(H, Q)
    right_residue = mul(P, power(omW, 7))
    require(left_residue == right_residue,
            'All-index residue-polynomial generating-function identity failed.')
    # The displayed partial fractions, cleared by the integer 7776 and Q.
    C = [1, 1, 1]
    partial_numerator = [0]
    for k, c in [(7, 561600), (6, -1404000), (5, 1263600),
                 (4, -491400), (3, 96732), (2, -13266), (1, -2521)]:
        partial_numerator = add(partial_numerator,
            scale(mul(mul(power(omz, 7-k), [1, 1]), power(C, 3)), c))
    partial_numerator = add(partial_numerator, scale(mul(power(omz, 7), power(C, 3)), -729))
    for j, numerator in [(1, [448, -1792]), (2, [-1536, -2496]), (3, [-1152, 1152])]:
        partial_numerator = add(partial_numerator,
            mul(numerator, mul(mul(power(omz, 7), [1, 1]), power(C, 3-j))))
    require(partial_numerator == scale(P, 7776),
            'All-index partial-fraction polynomial certificate failed.')
    require(P == P[::-1], 'Numerator is not palindromic.')
    require(Q == scale(Q[::-1], -1), 'Denominator is not antipalindromic.')
    require(evaluate(P, 1) == 3900 and evaluate(P, -1) == -12,
            'Pole numerator evaluations failed.')
    require(remainder_monic(P, [1, 1, 1]) == [12],
            'Primitive cube-root numerator remainder failed.')
    return {'gf_certificate_degree': len(lhs) - 1,
            'residue_certificate_degree': len(left_residue) - 1,
            'partial_fraction_certificate': '7776*Q*partial_fractions = 7776*P',
            'P_at_1': 3900, 'P_at_minus_1': -12,
            'P_mod_1_plus_z_plus_z2': [12]}


def source_audit() -> dict[str, object]:
    constants = [20736, 20045, 19712, 20493, 20288, 19496]
    linear = [42768, 42128, 42256, 42768, 42128, 42256]
    quadratic = [40788, 40692, 40788, 40788, 40692, 40788]
    differences = []
    for r in range(6):
        printed = [constants[r], linear[r], quadratic[r], 23400, 8125, 1560, 130]
        lhs = compose(printed, [r, 6])
        shifted = RESIDUES[r + 1] if r < 5 else compose(RESIDUES[0], [1, 1])
        diff = add(lhs, scale(shifted, -1296))
        require(diff == ([27] if r == 5 else [0]),
                'Printed-source comparison failed.')
        differences.append(diff)
    literal_n5 = Fraction(evaluate([constants[5], linear[5], quadratic[5],
                                   23400, 8125, 1560, 130], 5), 1296)
    require(literal_n5 == Fraction(598513, 48), 'Source arithmetic mismatch.')
    return {'printed_value_at_n5': str(literal_n5),
            'correct_A6': quasipolynomial(6),
            'printed_minus_shifted_numerator_by_residue': differences,
            'constant_correction': {'from': 19496, 'to': 19469},
            'indexing': 'Corrected printed expression at n equals A(n+1).'}


def mixed_bivariate_coefficients(nmax: int, mmax: int) -> list[list[int]]:
    """Expand the bivariate rational function, independently of orbit weights."""
    # Start with 1/((1-X)^3(1-Y)^3), then multiply (1+X)(1+Y).
    out = [[(n + 1) ** 2 * (m + 1) ** 2 for m in range(mmax + 1)]
           for n in range(nmax + 1)]
    # Geometric factors, with ascending in-place updates.
    for dn, dm in [(1, 2), (2, 3)]:
        for n in range(dn, nmax + 1):
            for m in range(dm, mmax + 1):
                out[n][m] += out[n - dn][m - dm]
    # Numerator 1+5XY^2+5X^2Y^3+X^3Y^5.
    result = [[0] * (mmax + 1) for _ in range(nmax + 1)]
    for dn, dm, c in [(0, 0, 1), (1, 2, 5), (2, 3, 5), (3, 5, 1)]:
        for n in range(dn, nmax + 1):
            for m in range(dm, mmax + 1):
                result[n][m] += c * out[n - dn][m - dm]
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path, default=Path(__file__).parent / 'data')
    args = parser.parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    started = time.perf_counter()
    checks: list[dict[str, object]] = []

    def record(name: str, **details: object) -> None:
        checks.append({'name': name, 'passed': True, **details})
        print(f'PASS: {name}', flush=True)

    cert = polynomial_certificates()
    record('Three all-index integer-polynomial certificates and pole tests', **cert)
    record('Exact printed-source shift and typographical-error audit', **source_audit())

    for n in range(3):
        value, candidates = brute_count(n)
        require(value == quasipolynomial(n), f'Original brute-force mismatch at {n}.')
        record(f'Independent original-grid enumeration, n={n}',
               arrays_tested=candidates, valid_arrays=value)

    # Basis checks prove that each linear grid relation vanishes under the map.
    for j in range(6):
        basis = tuple(int(j == k) for k in range(6))
        require(grid_valid(parametrization(*basis)), 'Linear parametrization test failed.')
        require(inverse(parametrization(*basis)) == basis, 'Linear inverse test failed.')
    record('Exact linear-map checks on the six coordinate basis vectors')

    for x in range(-20, 21):
        for y in range(-20, 21):
            points = orbit(x, y)
            reps = [(a, b) for a, b in points if a >= 2 * b >= 0]
            require(len(reps) == 1, 'Fundamental-domain uniqueness failed.')
            a, b = reps[0]
            require(len(points) == multiplicity(a - 2 * b, b), 'Orbit size mismatch.')
            require(all((h1(a, b), h2(a, b)) == (h1(x, y), h2(x, y))
                        for a, b in points), 'Norm invariance failed.')
    record('Dihedral orbit, chamber, and norm checks', grid='[-20,20]^2')

    for n in range(101):
        require(norm_count(n) == chamber_count(n), f'Norm/chamber mismatch at {n}.')
    record('Independent full-lattice sum versus chamber sum', indices='0..100')
    for n in range(301):
        require(chamber_count(n) == quasipolynomial(n), f'Chamber/quasipoly mismatch at {n}.')
    record('Positive chamber sum versus residue formula', indices='0..300')

    sequence = rational_coefficients(1000)
    require(sequence == [quasipolynomial(n) for n in range(1001)],
            'Rational-series coefficient mismatch.')
    require(sequence[1:30] == OEIS_FIRST, 'Published OEIS initial values mismatch.')
    record('Reduced rational function versus residue formula', indices='0..1000')
    record('All 29 initial values displayed on the retrieved OEIS page agree')

    for n in range(-200, 201):
        require(centered_formula(n) == quasipolynomial(n), 'Centered formula mismatch.')
        require(quasipolynomial(-n) == quasipolynomial(n - 2), 'Reciprocity mismatch.')
    record('Centered expression and quasipolynomial reciprocity', indices='-200..200')

    mixed = mixed_bivariate_coefficients(20, 20)
    for n in range(21):
        for m in range(21):
            value = mixed_count(n, m)
            require(value == mixed[n][m], 'Bivariate rational-function mismatch.')
            require(value == norm_count(n, m), 'Mixed full-lattice mismatch.')
    record('Two-bound counts: bivariate rational expansion, lattice sum, chamber sum',
           rectangle='0..20 by 0..20')

    with (args.output_dir / 'sequence.csv').open('w', newline='') as f:
        writer = csv.writer(f)
        writer.writerow(['n', 'A_n'])
        writer.writerows(enumerate(sequence))
    with (args.output_dir / 'two_bound_counts.csv').open('w', newline='') as f:
        writer = csv.writer(f)
        writer.writerow(['n', 'm', 'A_n_m'])
        writer.writerows((n, m, mixed[n][m]) for n in range(21) for m in range(21))
    report = {'status': 'all checks passed', 'python': platform.python_version(),
              'elapsed_seconds': round(time.perf_counter() - started, 3),
              'checks': checks, 'numerator_ascending': P, 'denominator_ascending': Q,
              'residue_coefficients_ascending': RESIDUES,
              'scope': 'Exact algebra certificates plus finite independent tests; not proof-assistant verification.'}
    (args.output_dir / 'verification.json').write_text(json.dumps(report, indent=2) + '\n')
    lines = ['A195806 verification report', f'Python {report["python"]}',
             f'Status: {report["status"]}', f'Elapsed: {report["elapsed_seconds"]} seconds', '']
    lines += [f'PASS: {item["name"]}\n  ' + '; '.join(f'{k}={v}' for k, v in item.items()
              if k not in ('name', 'passed')) for item in checks]
    lines += ['', str(report['scope'])]
    (args.output_dir / 'verification.txt').write_text('\n'.join(lines) + '\n')
    print(f'All {len(checks)} checks passed in {report["elapsed_seconds"]} seconds.')
    print(f'Reports and CSV files written to: {args.output_dir}')


if __name__ == '__main__':
    main()
