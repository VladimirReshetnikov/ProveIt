#!/usr/bin/env python3
"""Expand the worked example's complete sum-of-squares polynomial exactly."""
from __future__ import annotations
import json
from pathlib import Path
from polynomial_histories import (
    ONE, add, compile_system, encode_poly, example_ca, multiply,
    scale, witness_for_horizon,
)


def expand_quadratic(system):
    """Map monomials in UNKNOWN names to coefficient polynomials in Z[X,Y]."""
    result = {}
    for row in system.equations:
        terms = [((), row.constant)] + [((name,), p) for name, p in row.coefficients.items()]
        for i, (u, a) in enumerate(terms):
            for j in range(i, len(terms)):
                v, b = terms[j]
                key = tuple(sorted(u + v))
                coefficient = scale(multiply(a, b), 1 if i == j else 2)
                result[key] = add(result.get(key, {}), coefficient)
                if not result[key]:
                    del result[key]
    return result


def evaluate_expanded(quadratic, witness):
    result = {}
    for names, coefficient in quadratic.items():
        value = dict(coefficient)
        for name in names:
            value = multiply(value, witness[name])
        result = add(result, value)
    return result


def main():
    output = Path(__file__).resolve().parents[1] / "results"
    output.mkdir(parents=True, exist_ok=True)
    system = compile_system(example_ca(), (1, 0, 0, 0, 2))
    witness, _ = witness_for_horizon(system, 4)
    quadratic = expand_quadratic(system)
    assert not evaluate_expanded(quadratic, witness)
    checks = 1
    for name in ("D", "Q", "B", "V", "J", "T_0", "Z_0_0_0"):
        changed = {key: dict(p) for key, p in witness.items()}
        changed[name] = add(changed[name], ONE)
        residuals = system.residuals(changed)
        expected = add(*(multiply(r, r) for r in residuals.values()))
        assert evaluate_expanded(quadratic, changed) == expected and expected
        checks += 1
    terms = [{"unknowns": list(key), "coefficient": encode_poly(value)}
             for key, value in sorted(quadratic.items())]
    summary = {"unknowns": len(system.variables), "squared_residuals": len(system.equations),
               "degree_in_unknowns": max(map(len, quadratic)),
               "monomials_in_unknowns": len(quadratic),
               "fully_expanded_integer_terms": sum(len(p) for p in quadratic.values()),
               "max_coefficient_total_degree_in_X_Y": max(i+j for p in quadratic.values() for i,j in p),
               "exact_evaluation_checks": checks}
    with (output / "example_quadratic.json").open("w") as stream:
        json.dump({"domain_of_unknowns": "N[X,Y]", "meaning": "sum of all squared residuals = 0",
                   "statistics": summary, "terms": terms}, stream, indent=2)
    with (output / "quadratic_results.json").open("w") as stream:
        json.dump(summary, stream, indent=2)
    print(json.dumps(summary, indent=2))

if __name__ == "__main__":
    main()
