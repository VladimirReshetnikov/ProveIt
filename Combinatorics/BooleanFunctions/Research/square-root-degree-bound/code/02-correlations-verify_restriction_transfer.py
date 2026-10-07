#!/usr/bin/env python3
"""Exact finite checks of the signed-restriction and conjunction identities.

This is a finite regression certificate, not a proof of any general theorem.
It exhausts all 256 Boolean functions on three bits. Normalized Fourier
coefficients are evaluated directly from truth tables using Fraction; the
biases 1/5, 1/2, 4/5 have rational standard deviations 4/5, 1, 4/5.
Only the Python standard library is required. Run without python -O.
"""
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from math import comb, isqrt, prod
from pathlib import Path
import json

SIGNS = (-1, 1)
BIAS_SET = (F(1, 5), F(1, 2), F(4, 5))


@lru_cache(None)
def sigma(p):
    square = 4 * p * (1 - p)
    a, b = isqrt(square.numerator), isqrt(square.denominator)
    assert a * a == square.numerator and b * b == square.denominator
    return F(a, b)


@lru_cache(None)
def points(n):
    return tuple(product(SIGNS, repeat=n))


def index_of(x):
    result = 0
    for bit in x:
        result = 2 * result + (bit == 1)
    return result


@lru_cache(None)
def direct_kernel(biases):
    """Rows are P(X=x) times the normalized character, for every subset."""
    n = len(biases)
    rows = [[] for mask in range(1 << n)]
    for x in points(n):
        probability = prod((p if bit == 1 else 1 - p
                            for bit, p in zip(x, biases)), start=F(1))
        singletons = [(bit - (2 * p - 1)) / sigma(p) for bit, p in zip(x, biases)]
        characters = [F(1)] * (1 << n)
        for mask in range(1, 1 << n):
            low_bit = mask & -mask
            characters[mask] = characters[mask ^ low_bit] * singletons[low_bit.bit_length() - 1]
        for row, character in zip(rows, characters):
            row.append(probability * character)
    return tuple(tuple(row) for row in rows)


@lru_cache(None)
def direct_fourier(values, biases):
    return tuple(sum((value * weight for value, weight in zip(values, row)), F(0))
                 for row in direct_kernel(biases))


@lru_cache(None)
def uniform_fourier(values):
    """Independent integer Walsh transform, with the subset convention fixed."""
    transformed = list(values)
    size = len(values)
    n = size.bit_length() - 1
    width = 1
    while width < size:
        for start in range(0, size, 2 * width):
            for j in range(start, start + width):
                a, b = transformed[j], transformed[j + width]
                transformed[j], transformed[j + width] = a + b, a - b
        width *= 2
    result = []
    for mask in range(size):
        reverse = sum(((mask >> i) & 1) << (n - 1 - i) for i in range(n))
        result.append(F((-1) ** mask.bit_count() * transformed[reverse], size))
    return tuple(result)


def degree(coefficients):
    return max((mask.bit_count() for mask, value in enumerate(coefficients) if value),
               default=0)


def level_mass(coefficients, ell):
    return sum((abs(value) for mask, value in enumerate(coefficients)
                if mask.bit_count() == ell), F(0))


def derivative(coefficients, i, means):
    return sum((value * prod((means[j] for j in range(len(means))
                             if j != i and mask >> j & 1), start=F(1))
                for mask, value in enumerate(coefficients) if mask >> i & 1), F(0))


def channel(p, q, orientation):
    """List ((slope, constant), probability) of deterministic signed maps."""
    r = p if orientation == 1 else 1 - p
    retention = min(q / r, (1 - q) / (1 - r))
    fixed = -1 if q <= r else 1
    outcomes = [((orientation, 0), retention)]
    if retention < 1:
        outcomes.append(((0, fixed), 1 - retention))
    kappa = retention * sigma(p) / sigma(q)
    assert kappa * kappa == min(q * (1 - r) / (r * (1 - q)),
                                r * (1 - q) / (q * (1 - r)))
    return tuple(outcomes), kappa


def composed_truth(values, maps):
    return tuple(values[index_of(tuple(a * bit + b for bit, (a, b) in zip(x, maps)))]
                 for x in points(len(maps)))


def ordinary_truth(values, restriction):
    return composed_truth(values, tuple((1, 0) if bit == 0 else (0, bit)
                                        for bit in restriction))


def check_three_bits():
    source = (F(1, 5), F(1, 2), F(4, 5))
    target = (F(4, 5), F(1, 5), F(1, 2))
    uniform = (F(1, 2),) * 3
    means = tuple(2 * q - 1 for q in target)
    restrictions = tuple(product((-1, 0, 1), repeat=3))
    counters = dict(boolean_functions=0, deterministic_channel_outcomes=0,
                    all_subset_identities=0, degree_preservation_checks=0,
                    signed_existence_checks=0, weighted_level_checks=0,
                    ordinary_restrictions=0, direct_derivative_checks=0)
    map_types = set()
    singleton_signs = set()
    min_slack = None
    positive_slack_cases = 0
    for table_code in range(256):
        values = tuple(1 if table_code >> j & 1 else -1 for j in range(8))
        coefficients = uniform_fourier(values)
        assert coefficients == direct_fourier(values, uniform)
        outer_degree = degree(coefficients)
        target_coefficients = direct_fourier(values, target)
        ds = tuple(derivative(coefficients, i, means) for i in range(3))
        assert all(target_coefficients[1 << i] == sigma(target[i]) * ds[i]
                   for i in range(3))
        counters['direct_derivative_checks'] += 3
        orientations = tuple(1 if d >= 0 else -1 for d in ds)
        singleton_signs.update(0 if d == 0 else (1 if d > 0 else -1) for d in ds)
        channels = [channel(p, q, e) for p, q, e in zip(source, target, orientations)]
        assert all(kappa >= F(1, 4) for outcomes, kappa in channels)
        expected = [F(0)] * 8
        total_probability = F(0)
        best_signed = None
        for choices in product(*(outcomes for outcomes, kappa in channels)):
            maps = tuple(choice[0] for choice in choices)
            probability = prod((choice[1] for choice in choices), start=F(1))
            assert probability > 0
            map_types.update(maps)
            transformed = composed_truth(values, maps)
            hats = direct_fourier(transformed, source)
            assert degree(uniform_fourier(transformed)) <= outer_degree
            counters['degree_preservation_checks'] += 1
            for mask, value in enumerate(hats):
                expected[mask] += probability * value
            total_probability += probability
            signed = sum((hats[1 << i] for i in range(3)), F(0))
            best_signed = signed if best_signed is None else max(best_signed, signed)
            counters['deterministic_channel_outcomes'] += 1
        assert total_probability == 1
        for mask in range(8):
            factor = prod((orientations[i] * channels[i][1]
                           for i in range(3) if mask >> i & 1), start=F(1))
            assert expected[mask] == factor * target_coefficients[mask]
            counters['all_subset_identities'] += 1
        bound = sum((channels[i][1] * abs(target_coefficients[1 << i])
                     for i in range(3)), F(0))
        assert sum((expected[1 << i] for i in range(3)), F(0)) == bound
        assert best_signed >= bound
        slack = best_signed - bound
        min_slack = slack if min_slack is None else min(min_slack, slack)
        positive_slack_cases += (slack > 0)
        counters['signed_existence_checks'] += 1

        ordinary_max = [F(0)] * 4
        for restriction in restrictions:
            hats = uniform_fourier(ordinary_truth(values, restriction))
            assert degree(hats) <= outer_degree
            for ell in range(1, 4):
                ordinary_max[ell] = max(ordinary_max[ell], level_mass(hats, ell))
            counters['ordinary_restrictions'] += 1
        uniform_factors = [channel(F(1, 2), q, 1)[1] for q in target]
        assert all(k * k == (1 - abs(mu)) / (1 + abs(mu))
                   for k, mu in zip(uniform_factors, means))
        for ell in range(1, 4):
            weighted = sum((abs(value) * prod((uniform_factors[i] for i in range(3)
                                               if mask >> i & 1), start=F(1))
                            for mask, value in enumerate(target_coefficients)
                            if mask.bit_count() == ell), F(0))
            assert weighted <= ordinary_max[ell]
            assert level_mass(target_coefficients, ell) <= 2 ** ell * ordinary_max[ell]
            counters['weighted_level_checks'] += 1
        counters['boolean_functions'] += 1
    assert map_types == {(-1, 0), (1, 0), (0, -1), (0, 1)}
    assert singleton_signs == {-1, 0, 1}
    counters.update(source_biases=[str(p) for p in source],
                    target_biases=[str(q) for q in target],
                    all_four_map_types_exercised=True,
                    all_three_derivative_signs_exercised=True,
                    minimum_signed_existence_slack=str(min_slack),
                    positive_signed_existence_slack_cases=positive_slack_cases)
    return counters


def and_level_formula(n, ell, q):
    if n < ell:
        return F(0)
    return 2 * comb(n, ell) * q ** (n - ell) * (sigma(q) / 2) ** ell


def check_conjunctions():
    counts = dict(dimensions=list(range(1, 9)), ordinary_restrictions=0,
                  distinct_restricted_truth_tables=0,
                  exact_restriction_maxima=0, direct_biased_level_formulas=0,
                  zero_levels_above_dimension=0, small_bias_ratio_identities=0)
    maxima = {}
    for n in range(1, 9):
        values = tuple(1 if all(bit == 1 for bit in x) else -1 for x in points(n))
        observed = [F(0)] * 9
        distinct = set()
        for restriction in product((-1, 0, 1), repeat=n):
            distinct.add(ordinary_truth(values, restriction))
            counts['ordinary_restrictions'] += 1
        # All restrictions were enumerated; repeated truth tables need one transform.
        assert len(distinct) == 2 ** n + 1
        counts['distinct_restricted_truth_tables'] += len(distinct)
        for restricted_values in distinct:
            hats = uniform_fourier(restricted_values)
            for ell in range(1, 9):
                observed[ell] = max(observed[ell], level_mass(hats, ell))
        for ell in range(1, 9):
            predicted = max((F(comb(k, ell)) * F(2) ** (1 - k)
                             for k in range(ell, n + 1)), default=F(0))
            assert observed[ell] == predicted
            counts['exact_restriction_maxima'] += 1
            if n < ell:
                counts['zero_levels_above_dimension'] += 1
        for q in BIAS_SET:
            hats = direct_fourier(values, (q,) * n)
            for ell in range(1, 9):
                assert level_mass(hats, ell) == and_level_formula(n, ell, q)
                counts['direct_biased_level_formulas'] += 1
        if n % 2 == 0:
            ell = n // 2
            w = F(comb(2 * ell, ell)) * F(2) ** (1 - 2 * ell)
            assert observed[ell] == w
            for q in (F(1, 2), F(4, 5)):
                rho = 2 * q - 1
                assert and_level_formula(n, ell, q) / w == (1 + rho) ** ell * sigma(q) ** ell
                counts['small_bias_ratio_identities'] += 1
            candidates = {k: F(comb(k, ell)) * F(2) ** (1 - k)
                          for k in range(ell, 4 * ell + 1)}
            assert max(candidates.values()) == w
            maximizers = [k for k, value in candidates.items() if value == w]
            assert maximizers == [2 * ell - 1, 2 * ell]
            maxima[str(ell)] = dict(W_ell=str(w), maximizing_dimensions=maximizers)
    counts['unrestricted_formula_maxima_on_test_grid'] = maxima
    return counts


def main():
    assert __debug__, 'Assertions must be enabled; do not run with python -O.'
    certificate = {
        'status': 'PASS',
        'arithmetic': 'Exact fractions and integer Walsh transforms; standard library only.',
        'scope': 'Finite exhaustive checks only; no general theorem or asymptotic limit is certified.',
        'three_variable_exhaustion': check_three_bits(),
        'conjunction_checks': check_conjunctions(),
    }
    output = Path(__file__).resolve().parent.parent / 'data' / 'restriction_transfer_certificate.json'
    output.write_text(json.dumps(certificate, indent=2, sort_keys=True) + '\n', encoding='utf-8')
    print(json.dumps(certificate, sort_keys=True))


if __name__ == '__main__':
    main()
