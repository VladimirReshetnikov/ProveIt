#!/usr/bin/env python3
"""Exact finite sanity checks for Entire Automorphisms at Surreal Scales.

These checks do not certify the infinite Hahn-series proofs or novelty.
Run: python verify.py [--output verification-results.json]
Requires Python 3.10+ and SymPy (tested with 1.14.0).
"""
from __future__ import annotations

import argparse
import itertools
import json
import math
import platform
from pathlib import Path
from typing import Iterator

try:
    import sympy as sp
except ImportError as exc:
    raise SystemExit("SymPy is required. Install requirements.txt first.") from exc


def compositions(total: int, length: int) -> Iterator[tuple[int, ...]]:
    if length == 1:
        yield (total,)
    else:
        for first in range(total + 1):
            for rest in compositions(total - first, length - 1):
                yield (first,) + rest


def monomial(variables: tuple[sp.Symbol, ...], powers: tuple[int, ...]) -> sp.Expr:
    return sp.prod(var ** power for var, power in zip(variables, powers))


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def check_cardinal() -> dict:
    x = sp.Symbol("x")
    nodes = [sp.Rational(1), sp.Rational(2), sp.Rational(3), sp.Rational(5)]
    values = [sp.Rational(7), sp.Rational(-3, 2), sp.Rational(0), sp.Rational(11)]
    losses = [0, 1, 2, 3]
    product = sp.prod(1 - x / z for z in nodes)
    terms = []
    for i, z in enumerate(nodes):
        deleted = sp.prod(1 - x / w for j, w in enumerate(nodes) if j != i)
        denominator = deleted.subs(x, z)
        require(denominator != 0, "Cardinal denominator vanished")
        padding = 2 * losses[i] + 2
        terms.append(values[i] / denominator * deleted * (x / z) ** padding)
    interpolant = sp.expand(sum(terms))
    observed = [sp.simplify(interpolant.subs(x, z)) for z in nodes]
    require(observed == values, "Padded cardinal interpolation failed")
    return {"status": "passed", "nodes": list(map(str, nodes)),
            "values": list(map(str, values)), "padding_degrees": [2*c+2 for c in losses],
            "interpolant_degree": int(sp.degree(interpolant, x)),
            "product_degree": int(sp.degree(product, x)), "equalities_checked": len(nodes)}


def check_linear_division() -> dict:
    x = sp.Symbol("x")
    a = sp.Rational(-3, 2)
    h = 3*x**5 - 2*x**3 + sp.Rational(7, 3)*x + 5
    f = sp.Poly(sp.expand((x-a)*h), x)
    recovered = 0
    for n in range(f.degree()):
        coefficient = sum(f.nth(k)*a**(k-n-1) for k in range(n+1, f.degree()+1))
        recovered += coefficient*x**n
    require(sp.expand(recovered-h) == 0, "Linear-division coefficient formula failed")
    return {"status": "passed", "root": str(a), "dividend_degree": f.degree()}


def check_simplex(d: int) -> dict:
    variables = sp.symbols("x:" + str(d))
    eps = sp.Symbol("epsilon")
    if d == 2:
        x, y = variables
        u = x + y**2
        mapping = [u, y + u**3]
    elif d == 3:
        x, y, z = variables
        u, v = x + y**2, y + z**2
        mapping = [u, v, z + u**2]
    else:
        raise ValueError("Only dimensions two and three are configured")
    jacobian = sp.Matrix(mapping).jacobian(variables)
    jacobian_det = sp.expand(jacobian.det())
    require(jacobian_det == 1, "Shear composition did not have unit Jacobian")
    columns = []
    for coordinate in variables:
        column = []
        for component in mapping:
            difference = sp.expand(component.subs(coordinate, coordinate+eps) - component)
            quotient = sp.cancel(difference / eps)
            require(quotient.is_polynomial(*variables, eps), "Nonpolynomial normalized difference")
            column.append(quotient)
        columns.append(sp.Matrix(column))
    normalized = sp.Matrix.hstack(*columns)
    require(all(sp.expand(entry) == 0 for entry in
                (normalized.subs(eps, 0)-jacobian)), "Taylor linear part did not match")
    determinant = sp.expand(normalized.det())
    require(sp.expand(determinant.subs(eps, 0)-jacobian_det) == 0,
            "Normalized simplex determinant had the wrong constant coefficient")
    remainder = sp.cancel((determinant-jacobian_det)/eps)
    require(remainder.is_polynomial(*variables, eps), "Simplex remainder was not integral-polynomial")
    return {"status": "passed", "dimension": d, "map": list(map(str, mapping)),
            "jacobian_determinant": str(jacobian_det),
            "normalized_determinant_constant": str(determinant.subs(eps, 0)),
            "normalized_determinant_epsilon_degree": int(sp.degree(determinant, eps)),
            "remainder_polynomial": True}


def check_counts() -> dict:
    cases = []
    for d in range(2, 7):
        for maximum in range(1, 9):
            transverse = [alpha for r in range(maximum+1)
                          for alpha in compositions(r, d-1)]
            lifted = {(maximum-sum(alpha),) + alpha for alpha in transverse}
            full = set(compositions(maximum, d))
            expected = math.comb(maximum+d-1, d-1)
            require(lifted == full, "Generator jets did not cover homogeneous monomials")
            require(len(transverse) == len(lifted) == expected, "Generator count mismatch")
            cases.append({"d": d, "M": maximum, "count": expected})
    return {"status": "passed", "number_of_cases": len(cases), "cases": cases}


def check_fat_ideal(d: int, nodes: list[int], multiplicities: list[int], degree_bound: int) -> dict:
    variables = sp.symbols("x:" + str(d))
    x, transverse_variables = variables[0], variables[1:]
    maximum = max(multiplicities)
    generators = []
    for r in range(maximum+1):
        # Monic factors differ from normalized canonical products only by units.
        product = sp.prod((x-node)**max(m-r, 0) for node, m in zip(nodes, multiplicities))
        for alpha in compositions(r, d-1):
            generators.append(sp.expand(product * monomial(transverse_variables, alpha)))
    basis_powers = [alpha for degree in range(degree_bound+1) for alpha in compositions(degree, d)]
    polynomial_basis = [monomial(variables, alpha) for alpha in basis_powers]
    jet_rows = []
    generator_jet_checks = 0
    for node, multiplicity in zip(nodes, multiplicities):
        point = dict(zip(variables, [sp.Integer(node)] + [sp.Integer(0)]*(d-1)))
        for order in range(multiplicity):
            for alpha in compositions(order, d):
                def jet(expression: sp.Expr) -> sp.Expr:
                    for variable, count in zip(variables, alpha):
                        if count:
                            expression = sp.diff(expression, variable, count)
                    return expression.subs(point)
                row = [jet(term) for term in polynomial_basis]
                jet_rows.append(row)
                for generator in generators:
                    require(jet(generator) == 0, "A proposed generator failed a prescribed jet")
                    generator_jet_checks += 1
    matrix = sp.Matrix(jet_rows)
    expected_length = sum(math.comb(m+d-1, d) for m in multiplicities)
    actual_rank = matrix.rank()
    require(actual_rank == expected_length, "Finite jet map had unexpected rank")
    groebner = sp.groebner(generators, *variables, order="lex", domain=sp.QQ)
    kernel = matrix.nullspace()
    for vector in kernel:
        polynomial = sp.expand(sum(c*b for c, b in zip(vector, polynomial_basis)))
        remainder = groebner.reduce(polynomial)[1]
        require(remainder == 0, "Vanishing jet polynomial was outside the proposed ideal")
    return {"status": "passed", "dimension": d, "nodes": nodes,
            "multiplicities": multiplicities, "degree_bound": degree_bound,
            "generator_count": len(generators), "generators": list(map(str, generators)),
            "jet_rank": actual_rank, "expected_quotient_length": expected_length,
            "generator_jet_equalities_checked": generator_jet_checks,
            "kernel_basis_elements_reduced_to_zero": len(kernel)}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path(__file__).with_name("verification-results.json"))
    args = parser.parse_args()
    results = {
        "scope": "Exact finite symbolic sanity checks only; not formal verification of the article.",
        "python": platform.python_version(), "sympy": sp.__version__,
        "padded_cardinal_interpolation": check_cardinal(),
        "linear_division": check_linear_division(),
        "simplex_determinants": [check_simplex(2), check_simplex(3)],
        "homogeneous_jet_counts": check_counts(),
        "finite_fat_point_ideals": [check_fat_ideal(2, [1, 2, 4], [1, 3, 2], 8),
                                   check_fat_ideal(3, [1, 2], [1, 2], 5)],
        "overall_status": "passed"
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    print(f"All finite checks passed. Results: {args.output}")


if __name__ == "__main__":
    main()
