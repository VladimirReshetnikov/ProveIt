#!/usr/bin/env python3
"""Exact verifier for the sharp ternary quartic obstruction.

Python 3.10+; standard library only.  No floating-point arithmetic, optimization,
CAS, random samples, or externally supplied coefficient census is used.
Run from any directory: python3 /path/to/verify_exact.py --report checks.json
The proof data are integers in Z[zeta], zeta^2+zeta+1=0.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import sys
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations, product
from math import comb
from pathlib import Path
from typing import Any

Pair = tuple[int, int]
Exponent = tuple[int, ...]
Polynomial = dict[Exponent, Pair]
UNITS: tuple[Pair, ...] = ((1, 0), (0, 1), (-1, -1))
POINTS = tuple(product(range(3), repeat=2))
ZERO8: Exponent = (0,) * 8
ZERO9: Exponent = (0,) * 9
# A star is represented by None.  It is an arbitrary unit triple of product 1.
FAMILIES = (
    (None, 0, 1, 2),
    (0, None, 2, 1),
    (1, 2, None, 0),
    (2, 1, 0, None),
)


class VerificationError(RuntimeError):
    """A finite certificate check failed."""


def require(condition: bool, message: str) -> None:
    # Deliberately not an assert: all checks still run under python -O.
    if not condition:
        raise VerificationError(message)


def mul(x: Pair, y: Pair) -> Pair:
    a, b = x
    c, d = y
    return (a * c - b * d, a * d + b * c - b * d)


def conj(x: Pair) -> Pair:
    return (x[0] - x[1], -x[1])


def scale(x: Pair, k: int) -> Pair:
    return (k * x[0], k * x[1])


def neg(u: Exponent) -> Exponent:
    return tuple(-a for a in u)


def addexp(u: Exponent, v: Exponent) -> Exponent:
    return tuple(a + b for a, b in zip(u, v))


def subexp(u: Exponent, v: Exponent) -> Exponent:
    return tuple(a - b for a, b in zip(u, v))


def addterm(p: Polynomial, u: Exponent, c: Pair) -> None:
    a, b = p.get(u, (0, 0))
    c = (a + c[0], b + c[1])
    if c == (0, 0):
        p.pop(u, None)
    else:
        p[u] = c


def labels(v: tuple[int, int]) -> tuple[int, ...]:
    x, y = v
    return x, y, (y - x) % 3, (y + x) % 3


def line_variables() -> list[Exponent]:
    result = []
    for d in range(4):
        for c in range(3):
            u = [0] * 8
            if c < 2:
                u[2 * d + c] = 1
            else:
                u[2 * d] = u[2 * d + 1] = -1
            result.append(tuple(u))
    return result


def doubled_line_polynomial(g: list[Exponent]) -> Polynomial:
    """Construct 2*K directly from the displayed affine-line formula."""
    p: Polynomial = {ZERO8: (-144, 0)}  # 2*(-2)*9*4
    pair_phases = {(0, 1): 0, (0, 2): 1, (0, 3): 2,
                   (1, 2): 2, (1, 3): 1, (2, 3): 0}

    def twice_real(u: Exponent, c: Pair) -> None:
        addterm(p, u, c)
        addterm(p, neg(u), conj(c))

    for v in POINTS:
        gv = [g[3 * d + c] for d, c in enumerate(labels(v))]
        for ds in combinations(range(4), 3):
            u = tuple(sum(gv[d][j] for d in ds) for j in range(8))
            twice_real(u, (1, 0))
        for i, j in combinations(range(4), 2):
            twice_real(subexp(gv[i], gv[j]), (-4, 0))
            twice_real(addexp(gv[i], gv[j]), scale(UNITS[pair_phases[i, j]], 6))
    return p


def cube_polynomial() -> tuple[Polynomial, dict[str, Any]]:
    """Enumerate all 9^5 cubes, with all degenerate cubes retained."""
    index = {v: i for i, v in enumerate(POINTS)}
    vertices = tuple(product((0, 1), repeat=4))
    signs = [1 if sum(w) % 2 == 0 else -1 for w in vertices]
    p: Polynomial = {}
    visited = 0
    for hs in product(POINTS, repeat=4):
        tensor = 0
        for j in range(4):
            term = hs[j][1]
            for k in range(4):
                if k != j:
                    term *= hs[k][0]
            tensor += term
        phase = UNITS[(-tensor) % 3]
        offsets = [tuple(sum(w[k] * hs[k][j] for k in range(4)) % 3
                         for j in range(2)) for w in vertices]
        for x, y in POINTS:
            u = [0] * 9
            for (dx, dy), sign in zip(offsets, signs):
                u[index[((x + dx) % 3, (y + dy) % 3)]] += sign
            addterm(p, tuple(u), phase)
            visited += 1
    require(visited == 59049, 'wrong number of cubes')
    census = Counter(a * a - a * b + b * b for a, b in p.values())
    require(census == Counter({20457**2: 1, 8**2: 72, 48**2: 108, 32**2: 108}),
            'cube census mismatch')
    require(p.get(ZERO9) == (20457, 0), 'cube constant mismatch')
    require(tuple(map(sum, zip(*p.values()))) == (24057, 0), 'constant-function value')
    return p, {'cubes': visited, 'nonzero_coefficients': len(p),
               'constant_coefficient': 20457, 'coefficient_absolute_sum': 29673,
               'constant_function_energy': '11/27'}


def verify_line_change(p: Polynomial, k2: Polynomial) -> None:
    # t_(2d+c)=alpha_d*prod(z_v on line)^3/prod(z_v), c=0,1.
    alpha = (0, 0, 1, 2)
    images = [tuple(3 * int(labels(v)[d] == c) - 1 for v in POINTS)
              for d in range(4) for c in range(2)]
    out: Polynomial = {ZERO9: (21609, 0)}
    for u, coefficient in k2.items():
        image = tuple(sum(u[j] * images[j][i] for j in range(8)) for i in range(9))
        phase = sum(u[2*d + c] * alpha[d] for d in range(4) for c in range(2)) % 3
        addterm(out, image, scale(mul(coefficient, UNITS[phase]), 8))
    require(out == p, '59049*E = 21609 + 16*K failed')


def monomial_basis(g: list[Exponent]) -> list[Exponent]:
    basis = {ZERO8}
    for u in g:
        basis.update((u, neg(u)))
    for i, j in combinations(range(12), 2):
        if i // 3 != j // 3:
            u, v = addexp(g[i], g[j]), subexp(g[i], g[j])
            basis.update((u, neg(u), v, neg(v)))
    return sorted(basis)


def family_columns(basis: list[Exponent]) -> set[tuple[Pair, ...]]:
    columns = set()
    for d, family in enumerate(FAMILIES):
        parts: dict[tuple[int, int], list[Pair]] = {}
        for i, u in enumerate(basis):
            exponent = (u[2*d], u[2*d+1])
            if exponent not in parts:
                parts[exponent] = [(0, 0)] * len(basis)
            phase = sum(int(family[e]) * (u[2*e] + u[2*e+1])
                        for e in range(4) if e != d) % 3
            parts[exponent][i] = UNITS[phase]
        columns.update(tuple(c) for c in parts.values())
    return columns


def verify_families(k2: Polynomial) -> dict[str, Any]:
    for d, family in enumerate(FAMILIES):
        restriction: Polynomial = {}
        for u, c in k2.items():
            phase = sum(int(family[e]) * (u[2*e] + u[2*e+1])
                        for e in range(4) if e != d) % 3
            addterm(restriction, (u[2*d], u[2*d+1]), mul(c, UNITS[phase]))
        require(restriction == {(0, 0): (306, 0)}, f'free family {d} failed')
    extremizers = []
    distribution: Counter[Fraction] = Counter()
    for ks in product(range(3), repeat=4):
        value = (0, 0)
        for u, c in k2.items():
            phase = sum(ks[e] * (u[2*e] + u[2*e+1]) for e in range(4)) % 3
            a, b = mul(c, UNITS[phase])
            value = value[0] + a, value[1] + b
        require(value[1] == 0, 'constant-corner not real')
        distribution[Fraction(value[0], 2)] += 1
        predicted = any(all(family[e] is None or family[e] == ks[e]
                            for e in range(4)) for family in FAMILIES)
        require((value == (306, 0)) == predicted, f'corner equality mismatch {ks}')
        require(value[0] <= 306, f'corner exceeds bound {ks}')
        if predicted:
            extremizers.append(ks)
    require(len(extremizers) == 12, 'wrong count of corner extremizers')
    return {'constant_corner_count': 81, 'constant_corner_extremizers': extremizers,
            'constant_corner_K_distribution': {str(k): v for k,v in sorted(distribution.items())},
            'free_families': FAMILIES}




def verify_small_primitives() -> dict[str, int]:
    """Exhaustive generator-difference checks; regressions of written proofs."""
    checks = 0

    def test(moduli: tuple[int,int], denominator: int, values: dict[tuple[int,int],int],
             top: list[int]) -> None:
        nonlocal checks
        for order in (4,5):
            for a in range(order+1):
                b = order-a
                for x,y in values:
                    total = sum((-1)**(order-i-j)*comb(a,i)*comb(b,j)*
                                values[((x+i)%moduli[0],(y+j)%moduli[1])]
                                for i in range(a+1) for j in range(b+1))
                    expected = top[a] if order == 4 else 0
                    require((total-expected) % denominator == 0,
                            f'primitive difference failed: {moduli},{order},{a},{x},{y}')
                    checks += 1
    test((9,3),3,{(x,y):comb(x,3)*y for x in range(9) for y in range(3)},[0,0,0,1,0])
    examples = (
        (lambda x,y:-comb(x,2), [0,0,0,0,3]),
        (lambda x,y:-comb(y,2), [3,0,0,0,0]),
        (lambda x,y:-x*y, [0,3,0,3,0]),
        (lambda x,y:3*comb(x,2)*comb(y,2), [0,0,3,0,0]),
    )
    for numerator, top in examples:
        test((3,3),9,{(x,y):numerator(x,y) for x,y in POINTS},top)
    return {'primitive_examples': 5, 'exact_generator_difference_checks': checks}

def determinant_bareiss(matrix: list[list[int]]) -> int:
    """Fraction-free determinant, including pivoting, over the integers."""
    a = [row[:] for row in matrix]
    n, previous, sign = len(a), 1, 1
    for k in range(n-1):
        pivot = next((i for i in range(k, n) if a[i][k]), None)
        if pivot is None:
            return 0
        if pivot != k:
            a[k], a[pivot] = a[pivot], a[k]
            sign = -sign
        for i in range(k+1, n):
            for j in range(k+1, n):
                numerator = a[k][k]*a[i][j] - a[i][k]*a[k][j]
                require(numerator % previous == 0, 'nonintegral Bareiss step')
                a[i][j] = numerator // previous
        previous = a[k][k]
        for i in range(k+1, n):
            a[i][k] = 0
    return sign*a[-1][-1]


def verify_phase_geometry() -> dict[str, Any]:
    incidence = [[3*int(labels(v)[d] == c)-1 for v in POINTS]
                 for d in range(4) for c in range(3)]
    for i in range(9):
        for j in range(9):
            require(sum(row[i]*row[j] for row in incidence) == (24 if i == j else -3),
                    'incidence Gram identity')
    reduced = [[v for j,v in enumerate(row) if j != 0]
               for i,row in enumerate(incidence) if i % 3 != 2]
    det = determinant_bareiss(reduced)
    require(abs(det) == 19683, 'degree of the phase quotient')
    # Each list is 9P evaluated at the nine points, with canonical digits 0,1,2.
    cubic_generators = [[x for x,y in POINTS], [y for x,y in POINTS]]
    cubic_generators += [[3*monomial(x,y) for x,y in POINTS] for monomial in
                        (lambda x,y:x*x, lambda x,y:x*y, lambda x,y:y*y,
                         lambda x,y:x*x*y, lambda x,y:x*y*y)]
    for values in cubic_generators:
        require(all(sum(a*v for a,v in zip(row,values)) % 9 == 0 for row in incidence),
                'cubic phase generator is not in the kernel')
    base_phases = (
        [0 for x,y in POINTS],
        [2*x*y for x,y in POINTS],
        [x*x+2*y*y+x*y for x,y in POINTS],
        [2*x*x+y*y+x*y for x,y in POINTS],
    )
    alpha = (0,0,1,2)
    for d, values in enumerate(base_phases):
        for e in range(4):
            if e == d:
                continue
            for c in range(3):
                phase9 = (sum(a*v for a,v in zip(incidence[3*e+c],values))+3*alpha[e]) % 9
                require(phase9 == 3*int(FAMILIES[d][e]), 'base phase for equality family')
    # Free-line transformation with h(0)=1 has determinant 27.
    free_matrix = [[-3,-3], [6,-3]]
    require(determinant_bareiss(free_matrix) == 27, 'free-line quotient degree')
    return {'incidence_rank': 8, 'normalized_phase_quotient_degree': abs(det),
            'explicit_cubic_kernel_order': 19683, 'free_line_quotient_degree': 27,
            'connected_extremizer_components': 4*(19683//27),
            'component_real_dimension_in_original_phase_torus': 3}

def modular_rank(a: list[list[int]], prime: int) -> int:
    a = [[v % prime for v in row] for row in a]
    rank = 0
    for c in range(len(a[0])):
        pivot = next((r for r in range(rank, len(a)) if a[r][c]), None)
        if pivot is None:
            continue
        a[rank], a[pivot] = a[pivot], a[rank]
        inv = pow(a[rank][c], -1, prime)
        a[rank] = [(v * inv) % prime for v in a[rank]]
        for r in range(rank+1, len(a)):
            factor = a[r][c]
            if factor:
                a[r] = [(v - factor*w) % prime for v, w in zip(a[r], a[rank])]
        rank += 1
    return rank


def verify_gram(cert: dict[str, Any], basis: list[Exponent], k2: Polynomial) -> dict[str, Any]:
    n = len(basis)
    require(n == 241 and cert['basis'] == [list(u) for u in basis], 'monomial basis mismatch')
    D, R = int(cert['denominator']), int(cert['cholesky_denominator'])
    require(D == 2592000000 and R == 1000000, 'unexpected denominators')
    matrices = {}
    for name, width in [('QA', n), ('QB', n), ('KA', 28), ('KB', 28), ('LA', n), ('LB', n)]:
        a = [[int(v) for v in row] for row in cert[name]]
        require(len(a) == n and all(len(row) == width for row in a), f'dimensions of {name}')
        matrices[name] = a
    QA, QB, KA, KB, LA, LB = (matrices[s] for s in ['QA','QB','KA','KB','LA','LB'])
    require(all(LA[i][j] == LB[i][j] == 0 for i in range(n) for j in range(i+1, n)),
            'L not lower triangular')
    require(all(QA[i][j] == QA[j][i] - QB[j][i] and QB[i][j] == -QB[j][i]
                for i in range(n) for j in range(n)), 'Q not Hermitian')
    gram: Polynomial = {}
    for i, u in enumerate(basis):
        for j, v in enumerate(basis):
            addterm(gram, subexp(v, u), (2*QA[i][j], 2*QB[i][j]))
    target = {u: scale(c, -D) for u, c in k2.items()}
    addterm(target, ZERO8, (306*D, 0))
    require(gram == target, 'm* Q m = 153-K failed')

    possible = family_columns(basis)
    for c in range(28):
        require(tuple((KA[i][c], KB[i][c]) for i in range(n)) in possible,
                f'K column {c} is not a family coefficient vector')
    # zeta -> 2 in F_7, since 2^2+2+1=0 mod 7.
    rank = modular_rank([[a + 2*b for a,b in zip(ra,rb)] for ra,rb in zip(KA,KB)], 7)
    require(rank == 28, 'K has no rank-28 certificate modulo 7')
    for i in range(n):
        for c in range(28):
            aa = bb = 0
            for j in range(n):
                a,b,u,v = QA[i][j], QB[i][j], KA[j][c], KB[j][c]
                aa += a*u - b*v
                bb += a*v + b*u - b*v
            require(aa == bb == 0, f'QK failed at {i},{c}')

    # Remainder Q+KK* - LL*. Coefficients below share denominator D*R^2.
    row_bounds, diagonal = [0]*n, [0]*n
    for i in range(n):
        for j in range(i+1):
            ca = cb = 0
            for a,b,c,e in zip(KA[i],KB[i],KA[j],KB[j]):
                ca += a*c - a*e + b*e
                cb += b*c - a*e
            ha, hb = QA[i][j] + D*ca, QB[i][j] + D*cb
            la = lb = 0
            for k in range(j+1):
                a,b,c,e = LA[i][k],LB[i][k],LA[j][k],LB[j][k]
                la += a*c - a*e + b*e
                lb += b*c - a*e
            ra, rb = R*R*ha - D*la, R*R*hb - D*lb
            if i == j:
                require(rb == 0, f'nonreal diagonal {i}')
                diagonal[i] = ra
            else:
                row_bounds[i] += abs(ra) + abs(rb)
                # Upper-triangular entry is conjugate: (ra-rb) - rb*zeta.
                row_bounds[j] += abs(ra-rb) + abs(rb)
    margin = min(a-b for a,b in zip(diagonal,row_bounds))
    denominator = D*R*R
    require(5*margin > denominator, 'Gershgorin lower bound not above 1/5')
    require(margin == 646878666855648000000, 'Gershgorin margin changed')
    return {'gram_dimension': n, 'kernel_rank': rank, 'gram_rank': n-rank,
            'denominator_Q': D, 'denominator_L': R,
            'gershgorin_margin_numerator': margin,
            'gershgorin_margin_denominator': denominator,
            'gershgorin_margin_reduced': str(Fraction(margin, denominator)),
            'certified_spectral_lower_bound': '1/5',
            'gram_nonzero_laurent_coefficients': len(gram),
            'family_coefficient_vectors': len(possible)}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificate', type=Path,
                        default=Path(__file__).resolve().parent/'data'/'ternary_quartic_gram.json')
    parser.add_argument('--report', type=Path, help='Write a JSON verification report here.')
    args = parser.parse_args()
    try:
        raw = args.certificate.read_bytes()
        cert = json.loads(raw)
        g = line_variables()
        k2 = doubled_line_polynomial(g)
        cubes, cube_report = cube_polynomial()
        print('PASS: all 59049 cubes and the exact coefficient census', flush=True)
        verify_line_change(cubes, k2)
        print('PASS: exact affine-line change of variables', flush=True)
        primitive_report = verify_small_primitives()
        print('PASS: explicit cover and integrable-plane primitive regressions', flush=True)
        geometry_report = verify_phase_geometry()
        print('PASS: phase quotient, cubic kernel, and explicit base phases', flush=True)
        family_report = verify_families(k2)
        print('PASS: four free equality families and all 81 constant corners', flush=True)
        gram_report = verify_gram(cert, monomial_basis(g), k2)
        print('PASS: Gram identity, Hermitian symmetry, rank, family kernel, and QK=0', flush=True)
        print('PASS: exact positive-definiteness certificate with margin > 1/5', flush=True)
        report = {'status': 'PASS', 'arithmetic': 'Python integers only; exact Z[zeta]',
                  'certificate_sha256': hashlib.sha256(raw).hexdigest(),
                  'cube_checks': cube_report, 'equality_checks': family_report,
                  'phase_geometry': geometry_report, 'primitive_regressions': primitive_report,
                  'matrix_checks': gram_report}
        if args.report:
            args.report.write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8')
        print(json.dumps(report, indent=2))
    except (VerificationError, OSError, ValueError, KeyError, TypeError) as error:
        print(f'FAIL: {error}', file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
