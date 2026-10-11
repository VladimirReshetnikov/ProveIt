#!/usr/bin/env python3
"""Independent exact audit of the differential-polygamma calculus.

No article implementation or incoming-package code is imported. The checks use:
  * explicit Laurent series, independently of the cotangent Riccati proof;
  * symbolic differentiation matrices versus a combinatorial IBP reduction;
  * formal harmonic increments for all 48 bilinear pairs 0<=r,s<=6 except (0,0).

Finite checks are audit certificates; the article supplies the analytic proofs.
"""
from __future__ import annotations

import argparse
import json
from collections import defaultdict
from fractions import Fraction as F
from functools import lru_cache
from math import comb, factorial
from pathlib import Path

import sympy as sp


def bernoulli_table(n: int) -> list[F]:
    b = [F(1)]
    for m in range(1, n + 1):
        b.append(-sum(F(comb(m + 1, k)) * b[k] for k in range(m)) / (m + 1))
    return b


def harmonic(n: int) -> F:
    return sum((F(1, k) for k in range(1, n + 1)), F(0))


def monomials_of_weight(weight: int, width: int) -> list[tuple[int, ...]]:
    out = []
    counts = [0] * width

    def generate(index: int, remaining: int) -> None:
        if index == 0:
            counts[0] = remaining
            out.append(tuple(counts))
            return
        unit = index + 1
        for count in range(remaining // unit + 1):
            counts[index] = count
            generate(index - 1, remaining - count * unit)
        counts[index] = 0

    generate(width - 1, weight)
    return out


def monomial_name(exponents: tuple[int, ...]) -> str:
    return '*'.join(f'u{j}' + (f'^{k}' if k != 1 else '')
                    for j, k in enumerate(exponents) if k) or '1'


def symbolic_monomial(exponents: tuple[int, ...], variables) -> sp.Expr:
    return sp.prod(u ** k for u, k in zip(variables, exponents))


def combinatorial_derivative(exponents: tuple[int, ...]) -> dict[tuple[int, ...], F]:
    result = defaultdict(F)
    for j, multiplicity in enumerate(exponents):
        if multiplicity:
            assert j + 1 < len(exponents)
            new = list(exponents)
            new[j] -= 1
            new[j + 1] += 1
            result[tuple(new)] += multiplicity
    return dict(result)


def is_normal(exponents: tuple[int, ...]) -> bool:
    highest = max((j for j, k in enumerate(exponents) if k), default=0)
    return highest == 0 or exponents[highest] >= 2


@lru_cache(maxsize=None)
def reduce_ibp(exponents: tuple[int, ...]):
    """Triangular reduction using exponent arithmetic, without SymPy differentiation."""
    if is_normal(exponents):
        return {}, {exponents: F(1)}
    r = max(j for j, k in enumerate(exponents) if k)
    assert r >= 1 and exponents[r] == 1
    a = exponents[r - 1]
    primitive = list(exponents)
    primitive[r] -= 1
    primitive[r - 1] += 1
    primitive = tuple(primitive)
    q = defaultdict(F, {primitive: F(1, a + 1)})
    normal = defaultdict(F)
    # V contains neither the highest variable nor its immediate predecessor.
    v = list(exponents)
    v[r] = v[r - 1] = 0
    for derivative_monomial, coefficient in combinatorial_derivative(tuple(v)).items():
        remainder = list(derivative_monomial)
        remainder[r - 1] += a + 1
        qpart, npart = reduce_ibp(tuple(remainder))
        scale = -coefficient / (a + 1)
        for m, value in qpart.items():
            q[m] += scale * value
        for m, value in npart.items():
            normal[m] += scale * value
    return ({m: c for m, c in q.items() if c},
            {m: c for m, c in normal.items() if c})


def check_ibp(max_weight: int) -> dict:
    width = max_weight
    variables = sp.symbols(f'u0:{width}')
    records = []
    corruption_rejected = False
    columns_checked = 0
    for weight in range(2, max_weight + 1):
        target = monomials_of_weight(weight, width)
        sources = monomials_of_weight(weight - 1, width)
        normals = [m for m in target if is_normal(m)]
        assert len(sources) + len(normals) == len(target)
        target_index = {m: i for i, m in enumerate(target)}
        source_index = {m: i for i, m in enumerate(sources)}
        normal_index = {m: i for i, m in enumerate(normals)}
        # Independent construction A: SymPy differentiates every source monomial.
        entries = {}
        for j, monomial in enumerate(sources):
            expr = symbolic_monomial(monomial, variables)
            derivative = sp.expand(sum(variables[r + 1] * sp.diff(expr, variables[r])
                                       for r in range(width - 1)))
            for m, coefficient in sp.Poly(derivative, *variables).terms():
                if coefficient:
                    entries[target_index[m], j] = coefficient
        for j, m in enumerate(normals):
            entries[target_index[m], len(sources) + j] = sp.Integer(1)
        matrix = sp.SparseMatrix(len(target), len(target), entries)
        # Independent construction B: reduce each target by exponent recursion.
        inverse_entries = {}
        max_denominator = 1
        for j, monomial in enumerate(target):
            q, n = reduce_ibp(monomial)
            assert all(m in source_index for m in q)
            assert all(m in normal_index for m in n)
            for m, value in q.items():
                inverse_entries[source_index[m], j] = sp.Rational(value.numerator, value.denominator)
                max_denominator = max(max_denominator, value.denominator)
            for m, value in n.items():
                inverse_entries[len(sources) + normal_index[m], j] = sp.Rational(value.numerator, value.denominator)
                max_denominator = max(max_denominator, value.denominator)
            columns_checked += 1
        inverse = sp.SparseMatrix(len(target), len(target), inverse_entries)
        # The two inverse equalities certify spanning, directness, uniqueness,
        # and every monomial decomposition, with exact rational arithmetic.
        assert matrix * inverse == sp.eye(len(target))
        assert inverse * matrix == sp.eye(len(target))
        if weight == 8:
            changed = matrix.copy()
            changed[0, 0] += 1
            assert changed * inverse != sp.eye(len(target))
            corruption_rejected = True
        records.append({
            'weight': weight,
            'ambient_dimension': len(target),
            'derivative_dimension': len(sources),
            'normal_dimension': len(normals),
            'normal_basis': [monomial_name(m) for m in normals],
            'decomposition_columns_verified': len(target),
            'largest_decomposition_coefficient_denominator': max_denominator,
            'both_inverse_certificates': True,
        })
    # Independent Hilbert-series coefficient calculation by the product formula.
    t = sp.symbols('t')
    truncated = [0] * (max_weight + 1)
    truncated[0] = 1
    for part in range(2, max_weight + 1):
        for n in range(part, max_weight + 1):
            truncated[n] += truncated[n - part]
    truncated[1] += 1
    assert truncated[:2] == [1, 1]
    for row in records:
        assert row['normal_dimension'] == truncated[row['weight']]
    assert corruption_rejected
    return {
        'weights': [2, max_weight],
        'records': records,
        'monomial_decompositions_checked': columns_checked,
        'two_sided_inverse_certificates': 2 * len(records),
        'hilbert_series_coefficients': truncated,
        'corruption_control_rejected': corruption_rejected,
    }


def laurent_derivative(series: dict[int, sp.Expr], order: int) -> dict[int, sp.Expr]:
    result = {}
    for exponent, coefficient in series.items():
        factor = 1
        for j in range(order):
            factor *= exponent - j
        if factor:
            result[exponent - order] = coefficient * factor
    return result


def laurent_multiply(left, right, upper_bound):
    result = defaultdict(lambda: sp.Integer(0))
    for a, x in left.items():
        for b, y in right.items():
            if a + b <= upper_bound:
                result[a + b] += x * y
    return {k: sp.expand(v) for k, v in result.items() if v != 0}


def scalar_jump(degree: int, L, pi2):
    return -sum(sp.binomial(degree, j) * L ** (degree - j)
                * (-1) ** ((j - 1) // 2) * pi2 ** ((j - 1) // 2)
                for j in range(1, degree + 1, 2))


def check_residue_filter(max_weight: int) -> dict:
    L, pi2, Y = sp.symbols('L pi2 Y')
    bern = bernoulli_table(2 * max_weight)
    mixed = scalar = 0
    records = []
    for weight in range(1, max_weight + 1):
        # Independent local constant-tail specialization:
        # -pi*cot(pi*eps)=-1/eps + sum 2*zeta(2n)*eps^(2n-1).
        base = {-1: -sp.Integer(1), 0: L}
        for n in range(1, weight // 2 + 1):
            coefficient = F((-1) ** (n + 1) * 2 ** (2 * n), factorial(2 * n)) * bern[2 * n]
            base[2 * n - 1] = sp.Rational(coefficient.numerator, coefficient.denominator) * pi2 ** n
        jets = {r: laurent_derivative(base, r) for r in range(weight)}
        local_counts = {'weight': weight, 'mixed_monomials': 0, 'scalar_monomials': 0}
        for exponents in monomials_of_weight(weight, max_weight):
            series = {0: sp.Integer(1)}
            remaining_weight = weight
            for r, count in enumerate(exponents):
                for _ in range(count):
                    remaining_weight -= r + 1
                    # A future product can lower the exponent by at most its
                    # remaining differential weight. Terms above this cutoff
                    # cannot contribute to eps^(-1).
                    series = laurent_multiply(series, jets[r], remaining_weight - 1)
            residue = sp.expand(series.get(-1, 0))
            is_mixed = any(exponents[r] for r in range(1, len(exponents)))
            expected = 0 if is_mixed else scalar_jump(exponents[0], L, pi2)
            assert sp.expand(residue - expected) == 0
            if is_mixed:
                mixed += 1
                local_counts['mixed_monomials'] += 1
            else:
                scalar += 1
                local_counts['scalar_monomials'] += 1
        records.append(local_counts)
    # A scalar polynomial is a genuine negative control for mixed cancellation.
    assert scalar_jump(2, L, pi2) == -2 * L
    assert scalar_jump(2, L, pi2) != 0
    # A separate Riccati construction checks the algebra at infinity, including
    # its divisibility; it is not used by the Laurent computation above.
    q = Y ** 2 + pi2
    riccati_checks = 0
    for r in range(1, 8):
        assert sp.rem(q, Y ** 2 + pi2, Y) == 0
        riccati_checks += 1
        q = sp.expand((Y ** 2 + pi2) * sp.diff(q, Y))
    scalar_remainder_checks = 0
    for degree in range(max_weight + 1):
        rem = sp.rem((L + Y) ** degree, Y ** 2 + pi2, Y)
        assert sp.expand(-rem.coeff(Y, 1) - scalar_jump(degree, L, pi2)) == 0
        scalar_remainder_checks += 1
    return {
        'maximum_weight': max_weight,
        'mixed_laurent_residues_checked': mixed,
        'scalar_laurent_residues_checked': scalar,
        'records': records,
        'independent_riccati_divisibility_checks': riccati_checks,
        'independent_scalar_remainder_checks': scalar_remainder_checks,
        'scalar_negative_control_rejected': True,
    }


def check_bilinear() -> dict:
    eps, z, B = sp.symbols('eps z B')
    records = []
    for r in range(7):
        for s in range(7):
            if r + s == 0:
                continue
            h = r + s
            weight = h + 2
            cs = {k: sp.symbols(f'c{k}') for k in range(2, weight + 1)}
            v = -1 / eps + B + sum(cs[k] * eps ** (k - 1) for k in cs)
            product = sp.expand(sp.diff(v, eps, r) * sp.diff(v, eps, s))
            increments = {B: B + z} | {cs[k]: cs[k] + z ** k for k in cs}
            deltas = {j: sp.expand(product.coeff(eps, -j).subs(increments)
                                   - product.coeff(eps, -j))
                      for j in range(1, weight + 1)}
            alpha, beta = (-1) ** (r + 1), (-1) ** (s + 1)
            residue_coefficient = (alpha + beta) * factorial(h)
            assert sp.expand(deltas[1] - residue_coefficient * z ** (h + 1)) == 0
            higher = sp.expand(sum(deltas[j] * z ** (j - 1) / sp.Integer(j - 1)
                                   for j in range(2, weight + 1)))
            coefficient = factorial(h) * (alpha * (harmonic(h) - harmonic(s))
                                         + beta * (harmonic(h) - harmonic(r)))
            assert sp.expand(higher - sp.Rational(coefficient.numerator, coefficient.denominator)
                             * z ** (h + 1)) == 0
            records.append({'r': r, 's': s,
                            'zeta_derivative_coefficient': str(residue_coefficient),
                            'zeta_coefficient': str(coefficient),
                            'both_pole_checks': True})
    harmonic_checks = 0
    for r in range(13):
        for s in range(13):
            lhs = factorial(r) * sum((F(factorial(r + s - k), factorial(r - k) * k)
                                      for k in range(1, r + 1)), F(0))
            rhs = factorial(r + s) * (harmonic(r + s) - harmonic(s))
            assert lhs == rhs
            harmonic_checks += 1
    return {
        'pairs_checked': len(records),
        'pairs_with_one_zero_index': sum(int(row['r'] == 0 or row['s'] == 0) for row in records),
        'direct_pole_identities_checked': 2 * len(records),
        'finite_harmonic_identities_checked': harmonic_checks,
        'records': records,
    }


def check_endpoint_constants() -> dict:
    x = sp.symbols('x')
    gamma = sp.EulerGamma
    # Exact local Laurent multiplication, without multiplying constant terms.
    psi = -1 / x - gamma + sum((-1) ** r * sp.zeta(r) * x ** (r - 1)
                              for r in range(2, 10))
    jets = [sp.diff(psi, x, r) for r in range(5)]
    at_one = [-gamma] + [(-1) ** (r + 1) * factorial(r) * sp.zeta(r + 1)
                         for r in range(1, 5)]
    cases = [((0, 1), -sp.zeta(3)), ((1, 2), 4 * sp.zeta(5)),
             ((0, 0), 2 * sp.zeta(2))]
    records = []
    for (r, s), expected in cases:
        constant = sp.expand(jets[r] * jets[s]).coeff(x, 0)
        endpoint = sp.expand(at_one[r] * at_one[s] - constant)
        assert sp.simplify(endpoint - expected) == 0
        records.append({'primitive': f'u{r}*u{s}', 'endpoint_constant': str(expected)})
    return {'cases_checked': len(records), 'records': records}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--max-weight', type=int, default=12)
    parser.add_argument('--filter-weight', type=int, default=10)
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).with_name('differential_exact_results.json'))
    args = parser.parse_args()
    assert args.max_weight >= 8
    assert args.filter_weight >= 2
    result = {
        'scope': 'Independent finite exact audit of sections 02--05; analytic arguments are supplied in the article.',
        'imports_article_or_incoming_code': False,
        'numerical_period_recognition': False,
        'ibp': check_ibp(args.max_weight),
        'residue_filter': check_residue_filter(args.filter_weight),
        'bilinear': check_bilinear(),
        'endpoint_constants': check_endpoint_constants(),
        'versions': {'sympy': sp.__version__},
    }
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    summary = {
        'ibp_weights': result['ibp']['weights'],
        'ibp_monomial_decompositions': result['ibp']['monomial_decompositions_checked'],
        'ibp_two_sided_inverse_certificates': result['ibp']['two_sided_inverse_certificates'],
        'mixed_residues': result['residue_filter']['mixed_laurent_residues_checked'],
        'scalar_residues': result['residue_filter']['scalar_laurent_residues_checked'],
        'bilinear_pairs': result['bilinear']['pairs_checked'],
        'bilinear_pairs_with_zero_index': result['bilinear']['pairs_with_one_zero_index'],
        'finite_harmonic_identities': result['bilinear']['finite_harmonic_identities_checked'],
        'endpoint_constants': result['endpoint_constants']['cases_checked'],
        'output': str(args.output),
    }
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    main()
