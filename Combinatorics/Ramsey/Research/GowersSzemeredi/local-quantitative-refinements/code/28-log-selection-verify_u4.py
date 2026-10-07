#!/usr/bin/env python3
"""Exact certificates for the real U^2--U^4 norm-gap section.

Standard library only. No floating-point value decides a mathematical check.
The general theorems are proved in u4_section.tex. This program verifies the
finite counting identities, explicit examples, and rational comparisons.

Run: python3 verify_u4.py --output u4_exact_results.json
"""
from __future__ import annotations
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations, product
from pathlib import Path
import argparse
import json

F = Fraction
GENERIC_COEFFICIENTS = [
    222, 864, 4080, 9120, 25640, 31808, 55120, 49280, 52360,
    28320, 24160, 4256, 5920, 0, 0, 0, 222,
]
ORDER7_COEFFICIENTS = [
    222, 864, 4080, 9120, 25640, 31808, 56672, 56160, 69560,
    41760, 39664, 12800, 11760, 480, 560, 32, 222,
]


def face_polynomial(modulus: int = 0) -> list[int]:
    """Expand the displayed exact eight-vertex generating identity.

    modulus=0 means equality over Z, not an approximation to a large prime.
    The four-frequency expansion requires only 4^8 face assignments.
    """
    vertices = tuple(product((0, 1), repeat=3))
    by_moment: dict[tuple[int, ...], Counter] = defaultdict(Counter)
    for frequencies in product((-3, -1, 1, 3), repeat=8):
        total = sum(frequencies)
        if total % modulus if modulus else total:
            continue
        moment = tuple(sum(t * v[j] for t, v in zip(frequencies, vertices))
                       for j in range(3))
        if modulus:
            moment = tuple(t % modulus for t in moment)
        by_moment[moment][sum(abs(t) == 3 for t in frequencies)] += 1
    result = [0] * 17
    for moment, counts in by_moment.items():
        opposite = tuple((-t) % modulus if modulus else -t for t in moment)
        for j, cj in counts.items():
            for k, ck in by_moment[opposite].items():
                result[j + k] += cj * ck
    return result


def elementary_counts() -> dict:
    vertices3 = tuple(product((0, 1), repeat=3))
    counts = Counter(tuple(sum(v[j] for v in subset) for j in range(3))
                     for subset in combinations(vertices3, 4))
    multiplicities = dict(sorted(Counter(counts.values()).items()))
    assert multiplicities == {1: 14, 2: 12, 4: 6, 8: 1}
    assert sum(counts.values()) == 70
    assert sum(t*t for t in counts.values()) == 222

    vertices4 = tuple(product((0, 1), repeat=4))
    nonzero = vertices4[1:]
    balanced_six = []
    categories = Counter()
    for subset in combinations(nonzero, 6):
        if all(sum(v[j] for v in subset) == 4 for j in range(4)):
            balanced_six.append(subset)
            complement = tuple(tuple(1-b for b in v) for v in subset)
            a0 = sum(sum(v) == 0 for v in complement)
            a3 = sum(sum(v) == 3 for v in complement)
            categories[(a0, a3)] += 1
    assert len(balanced_six) == 27
    assert dict(categories) == {(0, 0): 3, (1, 0): 12, (1, 1): 12}

    dual = Counter()
    for signs in product((-1, 1), repeat=15):
        if all(sum(s*v[j] for s, v in zip(signs, nonzero)) == 0
               for j in range(4)):
            dual[sum(signs)] += 1
    assert dict(sorted(dual.items())) == {-5: 1, -3: 27, -1: 111,
                                         1: 111, 3: 27, 5: 1}
    assert 16 * 2 * dual[3] == 864

    order3 = Counter()
    for signs in product((-1, 1), repeat=16):
        constraints = (sum(signs),) + tuple(
            sum(s*v[j] for s, v in zip(signs, vertices4)) for j in range(4))
        if all(t % 3 == 0 for t in constraints):
            order3[sum(signs)] += 1
    assert dict(sorted(order3.items())) == {-12: 8, -6: 16, 0: 286, 6: 16, 12: 8}
    return {
        'four_subset_multiplicities': multiplicities,
        'pure_cosine_coefficient': 222,
        'single_third_harmonic_count': 864,
        'fixed_vertex_positive_third_harmonic_count': 27,
        '27_count_categories': {str(k): v for k, v in categories.items()},
        'dual_coefficients': dict(sorted(dual.items())),
        'order3_phase_coefficients': dict(sorted(order3.items())),
    }


def u2_energy_integer(values: list[int]) -> int:
    n = len(values)
    return sum(sum(values[x] * values[(x+h) % n] for x in range(n))**2
               for h in range(n))


def direct_u4_integer(values: list[int]) -> F:
    n = len(values)
    vertices = tuple(product((0, 1), repeat=4))
    total = 0
    for x, h1, h2, h3, h4 in product(range(n), repeat=5):
        directions = (h1, h2, h3, h4)
        term = 1
        for v in vertices:
            term *= values[(x + sum(a*b for a, b in zip(v, directions))) % n]
        total += term
    return F(total, n**5)


def check_five_point() -> dict:
    values = [0, 1, 1, -1, -1]
    n = len(values)
    assert sum(values) == 0
    u2 = F(u2_energy_integer(values), n**3)
    table = []
    for h in range(n):
        row = []
        for k in range(n):
            g = [values[x] * values[(x+h) % n] * values[(x+k) % n]
                 * values[(x+h+k) % n] for x in range(n)]
            row.append(u2_energy_integer(g))
        table.append(row)
    expected = [[52, 19, 19, 19, 19], [19, 6, 1, 1, 6],
                [19, 1, 6, 6, 1], [19, 1, 6, 6, 1], [19, 6, 1, 1, 6]]
    assert table == expected
    u4 = F(sum(map(sum, table)), n**5)
    assert u4 == direct_u4_integer(values)
    assert u2 == F(36, 125) and u4 == F(52, 625)
    ratio = u4/u2**4
    assert ratio == F(5078125, 419904) < F(111, 8)
    return {'values': values, 'U2_power4': str(u2), 'U4_power16': str(u4),
            'ratio': str(ratio), 'unnormalized_derivative_energy_table': table,
            'independent_direct_cube_check': 'PASS'}


# Arithmetic in Q[t]/(t^3+t^2-2t-1), t=zeta_7+zeta_7^{-1}.
# All explicit seven-point values and direct cube sums are integral here.
Triple = tuple[int, int, int]
ZERO: Triple = (0, 0, 0)
ONE: Triple = (1, 0, 0)
T: Triple = (0, 1, 0)


def add(a: Triple, b: Triple) -> Triple:
    return tuple(x+y for x, y in zip(a, b))


def sub(a: Triple, b: Triple) -> Triple:
    return tuple(x-y for x, y in zip(a, b))


def scale(c: int, a: Triple) -> Triple:
    return tuple(c*x for x in a)


def mul(a: Triple, b: Triple) -> Triple:
    c = [0] * 5
    for i in range(3):
        for j in range(3):
            c[i+j] += a[i]*b[j]
    for k in (4, 3):
        q = c[k]
        c[k] = 0
        c[k-3] += q
        c[k-2] += 2*q
        c[k-1] -= q
    return tuple(c[:3])


def direct_field_norm(values: list[Triple], dimension: int) -> F:
    n = len(values)
    vertices = tuple(product((0, 1), repeat=dimension))
    total = ZERO
    for arguments in product(range(n), repeat=dimension+1):
        x, directions = arguments[0], arguments[1:]
        term = ONE
        for v in vertices:
            index = (x + sum(a*b for a, b in zip(v, directions))) % n
            term = mul(term, values[index])
        total = add(total, term)
    assert total[1:] == (0, 0), total
    return F(total[0], n**(dimension+1))


def check_seven_point(coefficients: list[int]) -> dict:
    cosines = [(2, 0, 0), T]
    for _ in range(6):
        cosines.append(sub(mul(T, cosines[-1]), cosines[-2]))
    assert cosines[7] == (2, 0, 0)
    assert all(cosines[7-j] == cosines[j] for j in range(1, 7))
    values = [sub(scale(7, cosines[x]), cosines[(3*x) % 7]) for x in range(7)]
    total = ZERO
    for value in values:
        total = add(total, value)
    assert total == ZERO
    u2 = direct_field_norm(values, 2)
    u4 = direct_field_norm(values, 4)
    assert u2 == 4804
    predicted = sum(c*(-1)**j*7**(16-j) for j, c in enumerate(coefficients))
    assert u4 == predicted == 5465448865508028
    ratio = u4/u2**4
    assert ratio == F(1366362216377007, 133153321267264) < F(111, 8)
    return {'integral_number_field_values': values, 'U2_power4': str(u2),
            'U4_power16': str(u4), 'ratio': str(ratio),
            'direct_cyclotomic_cube_check': 'PASS'}


def rational_comparisons() -> dict:
    p = F(159, 160)
    assert F(599, 600)**4 < p
    assert F(1, 160) < F(9, 32)**4
    z = F(599, 600) - F(28, 111)*F(9, 32)
    assert z == F(5147, 5550)
    target = F(323, 160)**2
    assert F(111, 8)*z**16 > target
    assert F(131, 8)*p**4 > target
    assert F(160, 323) < F(1, 2)
    b = F(-1, 7)
    u4 = sum(c*b**j for j, c in enumerate(GENERIC_COEFFICIENTS))
    u2 = 2*(1+b**4)
    ratio = u4/u2**4
    assert u4 == F(5465198316262956, 33232930569601)
    assert u2 == F(4804, 2401)
    assert ratio == F(1366299579065739, 133153321267264)
    assert ratio < F(111, 8)
    return {'split_pair_mass': str(p), 'universal_R_lower_bound': str(target),
            'c4_upper_bound_squared': str(F(160, 323)),
            'dual_bracket_rational_lower_bound': str(z),
            'two_harmonic_parameter': str(b), 'generic_U2_power4': str(u2),
            'generic_U4_power16': str(u4), 'generic_ratio': str(ratio),
            'c4_lower_bound_fourth_power': str(1/ratio)}


def check_lifted_certificate(max_dimension: int = 8) -> dict:
    """Verify the explicit proof construction for several dimensions.

    This checks one recursively constructed coefficient assignment, not the
    exponentially larger complete d-cube polynomial.
    """
    plus = {(0, 1, 1, 1), (1, 0, 1, 1), (1, 1, 0, 1), (1, 1, 1, 0),
            (0, 0, 1, 1), (1, 1, 0, 0)}
    signs = {v: (3 if not any(v) else 1 if v in plus else -1)
             for v in product((0, 1), repeat=4)}
    records = []
    for d in range(4, max_dimension+1):
        assert sum(abs(a) == 3 for a in signs.values()) == 1
        assert sum(signs.values()) == 0
        assert all(sum(a*v[j] for v, a in signs.items()) == 0 for j in range(d))
        records.append({'dimension': d, 'vertices': len(signs),
                        'nonzero_linear_coefficient_certified': True,
                        'sufficient_character_order': 3*2**(d-1)+1})
        lifted = {(0,)+v: a for v, a in signs.items()}
        lifted.update({(1,)+v: (-1)**sum(v) for v in product((0, 1), repeat=d)})
        signs = lifted
    return {'checked_dimensions': records}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, default=Path('u4_exact_results.json'))
    args = parser.parse_args()
    generic = face_polynomial()
    order7 = face_polynomial(7)
    assert generic == GENERIC_COEFFICIENTS
    assert order7 == ORDER7_COEFFICIENTS
    output = {'status': 'PASS', 'arithmetic': 'integers and exact rational numbers only',
              'generic_polynomial_coefficients': generic,
              'order7_polynomial_coefficients': order7,
              'elementary_counts': elementary_counts(),
              'five_point_example': check_five_point(),
              'seven_point_example': check_seven_point(order7),
              'rational_comparisons': rational_comparisons(),
              'higher_dimension_construction': check_lifted_certificate(),
              'limitations': ['The general inequalities are proved in the article.',
                              'No numerical optimization certifies an extremum.',
                              'No Lean compilation or kernel verification is claimed.']}
    rendered = json.dumps(output, indent=2) + '\n'
    args.output.write_text(rendered, encoding='utf-8')
    print('PASS: all exact norm-gap checks; output:', args.output)


if __name__ == '__main__':
    main()
