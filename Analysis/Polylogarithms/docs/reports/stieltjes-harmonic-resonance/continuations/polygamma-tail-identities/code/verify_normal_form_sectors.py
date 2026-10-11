#!/usr/bin/env python3
"""Independent algebraic verification of the two all-order sectors.

The checker constructs Bell polynomials by their partition formula and uses
an independent SymPy expression reduction, rather than the production
module's inverse-gamma recurrence or tuple-based reduction implementation.
It checks the square and complete u0/u1 sectors through weight 16, then
compares the resulting normal form with the production implementation.
"""
from __future__ import annotations

import argparse
import importlib.util
import json
import math
from pathlib import Path

import sympy as sp


def integer_partitions(n, minimum=1):
    if not n:
        yield ()
    else:
        for part in range(minimum, n + 1):
            for tail in integer_partitions(n - part, part):
                yield (part,) + tail


def bell_by_partitions(m, variables):
    result = sp.S.Zero
    for partition in integer_partitions(m):
        multiplicities = {k: partition.count(k) for k in set(partition)}
        coefficient = sp.factorial(m)
        monomial = sp.S.One
        for part, count in multiplicities.items():
            coefficient *= sp.Rational(
                (-1) ** ((part - 1) * count),
                math.factorial(count) * math.factorial(part) ** count)
            monomial *= variables[part - 1] ** count
        result += coefficient * monomial
    return sp.expand(result)


def deriv(expr, variables):
    return sp.expand(sum(sp.diff(expr, variables[r]) * variables[r + 1]
                         for r in range(len(variables) - 1)))


def independent_reduction(expr, variables):
    """Whole-polynomial elimination in descending derivative order."""
    remainder = sp.expand(expr)
    primitive = sp.S.Zero
    for r in range(len(variables) - 1, 0, -1):
        # Only terms linear in u_r, containing no larger derivative, pivot.
        polynomial = sp.Poly(remainder, *variables)
        target = sp.S.Zero
        for powers, coefficient in polynomial.terms():
            if powers[r] == 1 and not any(powers[r + 1:]):
                monomial = sp.prod(variables[j] ** powers[j]
                                   for j in range(len(variables)))
                target += coefficient * monomial
        if target == 0:
            continue
        # Integrate the coefficient polynomial with respect to u_(r-1).
        antiderivative = sp.integrate(sp.expand(target / variables[r]),
                                     variables[r - 1])
        primitive += antiderivative
        remainder = sp.expand(remainder - deriv(antiderivative, variables))
    assert sp.expand(expr - remainder - deriv(primitive, variables)) == 0
    return sp.expand(remainder), sp.expand(primitive)


def run(maximum, production_path=None):
    variables = sp.symbols('u0:' + str(maximum + 1))
    production = None
    if production_path:
        spec = importlib.util.spec_from_file_location('production_normal_form',
                                                      production_path)
        production = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(production)
    results = []
    square_checks = 0
    for m in range(maximum + 1):
        bell = bell_by_partitions(m, variables)
        normal, primitive = independent_reduction(bell, variables)
        poly = sp.Poly(normal, *variables)
        assert all((sum(powers) - m) % 2 == 0 for powers, _ in poly.terms())
        for r in range(1, m // 2):
            if 2 * r + 2 > m:
                continue
            powers = [0] * len(variables)
            powers[0] = m - 2 * r - 2
            powers[r] = 2
            assert poly.coeff_monomial(tuple(powers)) == (
                (-1) ** r * sp.binomial(m, 2 * r + 2))
            square_checks += 1
        observed = normal.subs({u: 0 for u in variables[2:]})
        expected = variables[0] ** m
        for s in range(1, m // 4 + 1):
            expected -= (sp.binomial(m, 4 * s) * sp.factorial2(4 * s - 1)
                         / (4 * s * s - 1) * variables[0] ** (m - 4 * s)
                         * variables[1] ** (2 * s))
        assert sp.expand(observed - expected) == 0
        if production:
            pnormal, _ = production.normal_form(
                production.inverse_gamma_polynomial(m))
            assert sp.expand(production.as_expression(pnormal) - normal) == 0
        results.append({'weight': m, 'sector': str(observed),
                        'normal_monomial_count': len(poly.terms())})
    # Coefficients of the entire Shi generator: compare exact formal series.
    y = sp.Symbol('y')
    shi = sum(y ** (2 * k + 1) /
              ((2 * k + 1) * sp.factorial(2 * k + 1))
              for k in range(maximum // 4 + 1))
    generator = (sp.cosh(y) + sp.sinh(y) / y - y * shi) / 2
    target = 1 - sum(y ** (2 * s) /
                     (sp.factorial(2 * s) * (4 * s * s - 1))
                     for s in range(1, maximum // 4 + 1))
    assert sp.series(generator - target, y, 0, maximum // 2 + 1).removeO() == 0
    return {'maximum_weight': maximum, 'square_coefficient_checks': square_checks,
            'complete_sector_checks': maximum + 1,
            'independent_reduction': True,
            'production_comparison': bool(production),
            'shi_generator': 'passed', 'records': results}


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--maximum', type=int, default=16)
    parser.add_argument('--production', type=Path, default=Path(__file__).with_name('differential_normal_form.py'))
    parser.add_argument('--output', type=Path, default=Path(__file__).resolve().parents[1]/'verification/normal_form_sectors.json')
    args = parser.parse_args()
    result = run(args.maximum, args.production)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'records'}, indent=2))
