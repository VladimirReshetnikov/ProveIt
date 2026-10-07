#!/usr/bin/env python3
"""Exact regression checks for the all-degree Boolean phase-integration article.

Python 3.10+, standard library only.  This is not a proof assistant and does not
optimize over all complex functions.  Every reported finite test uses integers or
Fraction; continuous and arbitrary-dimensional theorems are proved in the paper.
Checks remain active under python -O.
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from itertools import combinations, combinations_with_replacement, product
from math import comb
from pathlib import Path
import json
import random


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def parity(x: int) -> int:
    return x.bit_count() & 1


def gf2_rank(rows: list[int] | tuple[int, ...]) -> int:
    pivots: dict[int, int] = {}
    for row in rows:
        while row:
            p = row.bit_length() - 1
            if p in pivots:
                row ^= pivots[p]
            else:
                pivots[p] = row
                break
    return len(pivots)


def bound(d: int) -> Fraction:
    return 1 - Fraction(d + 1, 2**d)


def model_bound(d: int, rho: int) -> int:
    return rho + sum(comb(rho, j) for j in range(1, min(rho, d - 2) + 1))


@lru_cache(maxsize=None)
def indices(n: int, degree: int) -> tuple[tuple[int, ...], ...]:
    return tuple(combinations_with_replacement(range(n), degree))


@lru_cache(maxsize=None)
def index_map(n: int, degree: int) -> dict[tuple[int, ...], int]:
    return {t: i for i, t in enumerate(indices(n, degree))}


def coeff(mask: int, n: int, degree: int, t: tuple[int, ...]) -> int:
    return (mask >> index_map(n, degree)[tuple(sorted(t))]) & 1


def integrable(mask: int, n: int, degree: int) -> bool:
    values: dict[tuple[int, ...], int] = {}
    for i, t in enumerate(indices(n, degree)):
        support = tuple(sorted(set(t)))
        bit = (mask >> i) & 1
        if support in values and values[support] != bit:
            return False
        values[support] = bit
    return True


def contract(mask: int, n: int, degree: int, z: int) -> int:
    out = 0
    for i, t in enumerate(indices(n, degree - 1)):
        val = 0
        for j in range(n):
            if (z >> j) & 1:
                val ^= coeff(mask, n, degree, (j,) + t)
        out |= val << i
    return out


def phi(mask: int, n: int, d: int, frozen: tuple[int, ...], a: int, b: int) -> int:
    return (coeff(mask, n, d, (a, a, b) + frozen)
            ^ coeff(mask, n, d, (a, b, b) + frozen))


@lru_cache(maxsize=None)
def radical_templates(n: int, d: int) -> tuple[tuple[tuple[int, ...], ...], tuple[tuple[int, ...], ...]]:
    """Rows of the two defect-flattening matrices as linear expressions in T."""
    im = index_map(n, d)
    def pexpr(frozen: tuple[int, ...], a: int, b: int) -> int:
        return ((1 << im[tuple(sorted((a, a, b) + frozen))])
                ^ (1 << im[tuple(sorted((a, b, b) + frozen))]))
    frozen_rows = []
    for rest in indices(n, d - 4):
        for a, b in combinations(range(n), 2):
            frozen_rows.append(tuple(pexpr((z,) + rest, a, b) for z in range(n)))
    pair_rows = []
    for frozen in indices(n, d - 3):
        for a in range(n):
            pair_rows.append(tuple(pexpr(frozen, a, b) for b in range(n)))
    return tuple(frozen_rows), tuple(pair_rows)


def ranks(mask: int, n: int, d: int) -> tuple[int, int]:
    tr, tk = radical_templates(n, d)
    def rows(templates: tuple[tuple[int, ...], ...]) -> list[int]:
        return [sum(parity(mask & entry) << j for j, entry in enumerate(row))
                for row in templates]
    rr = rows(tr)
    return gf2_rank(rr), gf2_rank(rr + rows(tk))


def canonical_mask(n: int, d: int, u: int, v: int) -> int:
    answer = 0
    for k, t in enumerate(indices(n, d)):
        bit = 0
        for i in range(d):
            term = (v >> t[i]) & 1
            for j in range(d):
                if j != i:
                    term &= (u >> t[j]) & 1
            bit ^= term
        answer |= bit << k
    return answer


def defect_signature(mask: int, n: int, d: int) -> tuple[int, ...]:
    return tuple(phi(mask, n, d, frozen, a, b)
                 for frozen in indices(n, d - 3)
                 for a, b in combinations(range(n), 2))


@lru_cache(maxsize=None)
def binary_constant_energy(d: int, mask: int) -> Fraction:
    """Independent exact cube recursion: the four possible last directions."""
    if d == 1:
        return Fraction(int(mask == 0))
    lo = mask & ((1 << d) - 1)
    hi = mask >> 1
    return (1 + binary_constant_energy(d - 1, lo)
            + binary_constant_energy(d - 1, hi)
            + binary_constant_energy(d - 1, lo ^ hi)) / 4


def binary_rho(d: int, mask: int) -> int:
    # Coefficient c_j means j copies of e_2.  Defect coefficients are
    # c_{j+1}+c_{j+2}.  Flattening its first frozen slot gives these two rows.
    s = d - 3
    q = ((mask >> 1) ^ (mask >> 2)) & ((1 << (s + 1)) - 1)
    return gf2_rank([q & ((1 << s) - 1), q >> 1])


def binary_census(max_degree: int) -> list[dict[str, object]]:
    output = []
    for d in range(3, max_degree + 1):
        counts: Counter[int] = Counter()
        maximum = Fraction(0)
        maximum_noncanonical = Fraction(0)
        equal = 0
        for mask in range(1 << (d + 1)):
            en = binary_constant_energy(d, mask)
            is_integrable = all(((mask >> j) & 1) == ((mask >> 1) & 1)
                                for j in range(1, d))
            if is_integrable:
                counts[0] += 1
                continue
            require(en <= bound(d), f'binary energy bound d={d}, tensor={mask}')
            maximum = max(maximum, en)
            equal += int(en == bound(d))
            if d >= 4:
                rho = binary_rho(d, mask)
                require(rho > 0, 'nonintegrable binary tensor has zero defect rank')
                counts[rho] += 1
                cap = 1 - Fraction(d, 2**(d - 1)) * (1 - Fraction(1, 2**rho))
                require(en <= cap, 'rank-sensitive bound on constant test')
                if rho >= 2:
                    maximum_noncanonical = max(maximum_noncanonical, en)
                    require(en < bound(d), 'noncanonical endpoint')
                if en == bound(d):
                    require(rho == 1, 'endpoint has wrong radical')
            else:
                counts[1] += 1
        require(counts[0] == 8, 'binary integrable count')
        require(maximum == bound(d), 'binary constant sharpness')
        if d >= 4:
            require(counts[1] == 24, 'binary three flags times eight gauges')
        output.append({'degree': d, 'tensors': 1 << (d + 1),
                       ('contraction_rank_counts' if d >= 4 else 'cubic_half_defect_rank_counts'):
                           dict(sorted(counts.items())),
                       'maximum_nonintegrable_constant_energy': str(maximum),
                       'constant_endpoint_tensors': equal,
                       'maximum_noncanonical_constant_energy':
                           str(maximum_noncanonical) if d >= 4 and counts[2] else None})
    return output


def ternary_quartic_census() -> dict[str, object]:
    n, d = 3, 4
    counts: Counter[int] = Counter()
    models: Counter[tuple[int, int]] = Counter()
    # There are 21 flags line < plane in (F_2^3)^*.
    canonical_defects = {defect_signature(canonical_mask(n, d, u, v), n, d)
                         for u in range(1, 2**n) for v in range(1, 2**n) if v != u}
    require(len(canonical_defects) == 21, 'ternary flag count')
    for mask in range(1 << len(indices(n, d))):
        rho, effective = ranks(mask, n, d)
        counts[rho] += 1
        models[(rho, effective)] += 1
        require((rho == 0) == integrable(mask, n, d), 'integrability/radical equivalence')
        require(effective <= model_bound(d, rho), 'effective dimension bound')
        if rho == 1:
            require(defect_signature(mask, n, d) in canonical_defects,
                    'rank-one defect not canonical')
            require(effective == 2, 'canonical minimal model dimension')
    require(counts[0] == 128, 'ternary quartic integrable count')
    require(counts[1] == 21 * 128, 'ternary quartic flag/gauge count')
    return {'tensors': 32768, 'integrable_tensors': counts[0],
            'extremal_gauge_classes': len(canonical_defects),
            'rank_one_tensors': counts[1], 'rank_counts': dict(sorted(counts.items())),
            'rank_and_effective_dimension_counts':
                {f'{r},{m}': c for (r, m), c in sorted(models.items())}}


def sharp_model(d: int, rho: int) -> tuple[int, int, tuple[tuple[int, ...], ...]]:
    subsets = tuple(A for j in range(1, min(rho, d - 2) + 1)
                    for A in combinations(range(rho), j))
    n = rho + len(subsets)
    mask = 0
    for i, t in enumerate(indices(n, d)):
        rs = [a for a in t if a >= rho]
        hs = [a for a in t if a < rho]
        if len(rs) == 1 and tuple(sorted(set(hs))) == subsets[rs[0] - rho]:
            mask |= 1 << i
    return n, mask, subsets


def sharp_model_checks() -> list[dict[str, int]]:
    output = []
    for d, rho in product(range(4, 8), range(1, 4)):
        n, mask, subsets = sharp_model(d, rho)
        r, effective = ranks(mask, n, d)
        require(r == rho, f'sharp model contraction rank d={d}, rho={rho}')
        require(effective == n == model_bound(d, rho), 'sharp model complete rank')
        checks = 0
        for j, A in enumerate(subsets):
            rz = rho + j
            require(integrable(contract(mask, n, d, 1 << rz), n, d - 1),
                    'radical slice of sharp model not integrable')
            for t in indices(rho, d - 2):
                # Psi_r(z...,b) = Phi(z...)(r,b).
                val = phi(mask, n, d, t[1:], rz, t[0])
                require(val == int(tuple(sorted(set(t))) == A), 'Psi isomorphism')
                checks += 1
        output.append({'degree': d, 'rho': rho, 'ambient_dimension': n,
                       'minimal_model_dimension': effective,
                       'tensor_coefficients': len(indices(n, d)),
                       'psi_basis_checks': checks})
    return output


# Gaussian integers divided by a power of 2: denominator handled separately.
GI = tuple[int, int]

def mul(z: GI, w: GI) -> GI:
    return z[0]*w[0]-z[1]*w[1], z[0]*w[1]+z[1]*w[0]


def conjugate(z: GI) -> GI:
    return z[0], -z[1]


def derivative(values: tuple[GI, ...], h: int) -> tuple[GI, ...]:
    return tuple(mul(values[x ^ h], conjugate(values[x])) for x in range(len(values)))


@lru_cache(maxsize=None)
def eval_expression(n: int, d: int, vectors: tuple[int, ...]) -> int:
    im = index_map(n, d)
    out = 0
    choices = [tuple(i for i in range(n) if (x >> i) & 1) for x in vectors]
    for t in product(*choices):
        out ^= 1 << im[tuple(sorted(t))]
    return out


def selected_energy(values: tuple[GI, ...], denominator: int, n: int,
                    d: int, mask: int) -> Fraction:
    N = 1 << n
    total = 0
    for directions in product(range(N), repeat=d - 1):
        vals = values
        for h in directions:
            vals = derivative(vals, h)
        real, imag = 0, 0
        for x, z in enumerate(vals):
            sign = 1 - 2 * parity(mask & eval_expression(n, d, directions + (x,)))
            real += sign * z[0]
            imag += sign * z[1]
        total += real*real + imag*imag
    return Fraction(total, N**(d + 1) * denominator**(2**d))


def cube_energy(values: tuple[GI, ...], denominator: int, n: int,
                d: int, mask: int) -> Fraction:
    N = 1 << n
    re, im = 0, 0
    for directions in product(range(N), repeat=d):
        vals = values
        for h in directions:
            vals = derivative(vals, h)
        sign = 1 - 2 * parity(mask & eval_expression(n, d, directions))
        re += sign * sum(z[0] for z in vals)
        im += sign * sum(z[1] for z in vals)
    require(im == 0, 'cube energy is not real')
    return Fraction(re, N**(d + 1) * denominator**(2**d))


def function_checks() -> dict[str, int]:
    rng = random.Random(20261006)
    alphabet: tuple[GI, ...] = ((0, 0), (2, 0), (-2, 0), (0, 2), (0, -2),
                               (1, 1), (1, -1), (-1, 1), (-1, -1))
    counts: Counter[str] = Counter()
    for n, d, trials in ((2, 3, 18), (2, 4, 18), (3, 3, 10)):
        N = 1 << n
        for trial in range(trials):
            values = tuple(rng.choice(alphabet) for _ in range(N))
            mask = rng.getrandbits(len(indices(n, d)))
            en = selected_energy(values, 2, n, d, mask)
            require(en == cube_energy(values, 2, n, d, mask), 'selected/cube identity')
            sliced = sum((selected_energy(derivative(values, z), 4, n, d - 1,
                                          contract(mask, n, d, z)) for z in range(N)),
                         Fraction(0)) / N
            require(en == sliced, 'exact slicing identity')
            counts['selected_cube_and_slicing_tests'] += 1
            if not integrable(mask, n, d):
                require(en <= bound(d), 'nonintegrable energy test')
                counts['nonintegrable_function_tests'] += 1
            canonical = canonical_mask(n, d, 1, 2)
            require(selected_energy(values, 2, n, d, canonical) <= bound(d),
                    'canonical energy test')
            counts['canonical_function_tests'] += 1
            for directions in product(range(N), repeat=min(d - 1, 3)):
                vals = values
                for h in directions:
                    vals = derivative(vals, h)
                for h in directions:
                    require(all(vals[x ^ h] == conjugate(vals[x]) for x in range(N)),
                            'odd direction conjugation')
                    counts['translation_conjugation_vector_checks'] += 1
                for h in directions:
                    period = h ^ directions[0]
                    require(all(vals[x ^ period] == vals[x] for x in range(N)),
                            'even-direction period')
                    counts['even_period_vector_checks'] += 1
            m = d - 1
            pure = 1 << index_map(n, m)[(0,) * m]
            for z in range(N):
                if not (z & 1):
                    fixed = selected_energy(derivative(values, z), 4, n, m, pure)
                    require(fixed <= 1 - Fraction(1, 2**(m - 1)), 'fixed derivative cap')
                    counts['fixed_derivative_tests'] += 1
    return dict(counts)


def lowering_checks() -> dict[str, int]:
    rng = random.Random(47)
    total = 0
    for n, degree in product(range(1, 5), range(3, 8)):
        supports = tuple(A for j in range(1, min(n, degree) + 1)
                         for A in combinations(range(n), j))
        for _ in range(12):
            sc = {A: rng.randrange(2) for A in supports}
            mask = sum(sc[tuple(sorted(set(t)))] << i
                       for i, t in enumerate(indices(n, degree)))
            lowered = sum(coeff(mask, n, degree, (t[0],) + t) << i
                          for i, t in enumerate(indices(n, degree - 1)))
            require(integrable(lowered, n, degree - 1), 'diagonal lowering')
            total += 1
            for z in range(1 << n):
                require(integrable(contract(mask, n, degree, z), n, degree - 1),
                        'ordinary contraction of integrable tensor')
                total += 1
    return {'lowering_and_contraction_tests': total}


def normal_form_dimension_checks() -> dict[str, object]:
    records = []
    for n, d in product(range(2, 7), range(4, 8)):
        templates, _ = radical_templates(n, d)
        coefficients = len(indices(n, d))
        integrable_dimension = sum(comb(n, j) for j in range(1, min(n, d) + 1))
        for r in range(n + 1):
            # R_0 is spanned by basis vectors r,...,n-1. Each expression
            # below is a linear constraint on the COEFFICIENTS of T.
            constraints = [row[z] for row in templates for z in range(r, n)]
            quotient_dimension = coefficients - gf2_rank(constraints) - integrable_dimension
            target_dimension = (comb(r + d - 1, d)
                                - sum(comb(r, j) for j in range(1, min(r, d) + 1))
                                + (n - r) * sum(comb(r, j)
                                                for j in range(1, min(r, d - 2) + 1)))
            require(quotient_dimension == target_dimension, 'fixed radical normal-form dimension')
            records.append({'n': n, 'degree': d, 'quotient_dimension': quotient_dimension,
                            'fixed_complement_dimension': r})
    return {'parameter_cases': len(records), 'cases': records}


def algebra_checks() -> dict[str, object]:
    for d in range(4, 1001):
        rec = Fraction(1, 4) + Fraction(1, 4)*(1-Fraction(1, 2**(d-2))) + bound(d-1)/2
        require(rec == bound(d), 'canonical recurrence')
        noncanonical = 1 - Fraction(3*d, 2**(d+1))
        require(bound(d)-noncanonical == Fraction(d-2, 2**(d+1)) > 0,
                'strict induction separation')
    return {'recurrence_degrees': [4, 1000],
            'thresholds': {str(d): str(bound(d)) for d in range(3, 13)},
            'model_bounds': {str(d): {str(r): model_bound(d, r) for r in range(1, 6)}
                             for d in range(4, 9)}}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-degree', type=int, default=12)
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).resolve().parents[1] / 'data' / 'verification.json')
    args = parser.parse_args()
    if not 4 <= args.max_degree <= 16:
        parser.error('--max-degree must be between 4 and 16')
    report: dict[str, object] = {'status': 'passed', 'arithmetic': 'integers and exact fractions',
                                'seed': 20261006, 'proof_assistant': False,
                                'continuous_optimization_performed': False}
    for name, procedure in (
        ('algebra', algebra_checks),
        ('binary_census', lambda: binary_census(args.max_degree)),
        ('ternary_quartic_census', ternary_quartic_census),
        ('sharp_model_constructions', sharp_model_checks),
        ('integrable_lowering', lowering_checks),
        ('fixed_radical_normal_form', normal_form_dimension_checks),
        ('complex_function_regressions', function_checks),
    ):
        print(f'Checking {name}...', flush=True)
        report[name] = procedure()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
    print(f'All finite checks passed. Report: {args.output}')


if __name__ == '__main__':
    main()
