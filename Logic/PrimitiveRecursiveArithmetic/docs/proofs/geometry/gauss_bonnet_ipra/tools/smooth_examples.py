#!/usr/bin/env python3
"""Exact and numerical diagnostics for the constructive Gauss--Bonnet report.

The conformal example uses fractions.Fraction only.  The spherical example
checks finite symbolic identities with SymPy and performs high-precision
quadrature with mpmath.  These are implementation diagnostics, not Lean proofs,
not iPRA derivations, and not interval-certified numerical error bounds.

Usage (from the archive root):
    python3 tools/smooth_examples.py --output examples/smooth_results.json
"""

from __future__ import annotations

import argparse
from fractions import Fraction as Q
from math import comb, factorial
from pathlib import Path
import json
import platform


def poly_derivative(poly, axis):
    """Differentiate a finite rational bivariate polynomial."""
    out = {}
    for powers, coefficient in poly.items():
        degree = powers[axis]
        if degree:
            reduced = list(powers)
            reduced[axis] -= 1
            key = tuple(reduced)
            out[key] = out.get(key, Q(0)) + degree * coefficient
    return out


def triangle_integral(poly):
    """Integral over x>=0, y>=0, x+y<=1; exact monomial formula."""
    return sum(
        (coefficient * Q(factorial(i) * factorial(j), factorial(i + j + 2))
         for (i, j), coefficient in poly.items()),
        Q(0),
    )


def affine_path_integral(poly, start, stop):
    """Integral_0^1 poly(start+t*(stop-start)) dt, using finite binomial sums."""
    x0, y0 = map(Q, start)
    dx, dy = Q(stop[0]) - x0, Q(stop[1]) - y0
    return sum(
        (coefficient * comb(i, r) * comb(j, s)
         * x0 ** (i - r) * dx ** r * y0 ** (j - s) * dy ** s
         / (r + s + 1)
         for (i, j), coefficient in poly.items()
         for r in range(i + 1) for s in range(j + 1)),
        Q(0),
    )


def line_integral(p, q, start, stop):
    return ((Q(stop[0]) - Q(start[0])) * affine_path_integral(p, start, stop)
            + (Q(stop[1]) - Q(start[1])) * affine_path_integral(q, start, stop))


def conformal_example():
    potential = {(2, 0): Q(1), (1, 1): Q(2), (0, 2): Q(3)}
    ux = poly_derivative(potential, 0)
    uy = poly_derivative(potential, 1)
    omega_x = {key: -value for key, value in uy.items()}
    omega_y = ux
    curl = poly_derivative(omega_y, 0)
    for key, value in poly_derivative(omega_x, 1).items():
        curl[key] = curl.get(key, Q(0)) - value
    rho = {key: -value for key, value in curl.items()}
    vertices = [(0, 0), (1, 0), (0, 1)]
    edges = [(vertices[i], vertices[(i + 1) % 3]) for i in range(3)]
    edge_integrals = [line_integral(omega_x, omega_y, a, b) for a, b in edges]
    curvature_integral = triangle_integral(rho)
    # Conformality preserves angles; the three coordinate directions are fixed.
    interior_angles_over_pi = [Q(1, 2), Q(1, 4), Q(1, 4)]
    exterior_angles_over_pi = [1 - a for a in interior_angles_over_pi]
    assert rho == {(0, 0): Q(-8)}
    assert curvature_integral == -4
    assert edge_integrals == [Q(-1), Q(6), Q(-1)]
    assert curvature_integral + sum(edge_integrals) == 0
    assert sum(exterior_angles_over_pi) == 2
    return {
        "metric": "g = exp(2u) (dx^2 + dy^2)",
        "potential": "u = x^2 + 2*x*y + 3*y^2",
        "connection_convention": "omega = <nabla e1,e2> = -u_y dx + u_x dy",
        "curvature_density": "rho = -(u_xx + u_yy) = -8",
        "curvature_integral_exact": str(curvature_integral),
        "oriented_edges": [[list(a), list(b)] for a, b in edges],
        "edge_omega_integrals_exact": list(map(str, edge_integrals)),
        "edge_geodesic_curvature_integrals_exact": list(map(str, edge_integrals)),
        "interior_angles_over_pi": list(map(str, interior_angles_over_pi)),
        "exterior_angles_over_pi": list(map(str, exterior_angles_over_pi)),
        "rational_part_of_gb_residual": "0",
        "pi_coefficient_of_gb_residual": "0",
        "arithmetic": "Exact fractions.Fraction arithmetic; all assertions passed",
    }


def spherical_example(dps):
    import sympy as sp
    import mpmath as mp

    u, v = sp.symbols("u v", real=True)
    variables = (u, v)
    w = 1 - u - v
    s = u * u + v * v + w * w
    p, q = u - w, v - w
    E = 2 / s - p * p / s ** 2
    F = 1 / s - p * q / s ** 2
    G = 2 / s - q * q / s ** 2
    g = sp.Matrix([[E, F], [F, G]])
    ginv = g.inv().applyfunc(sp.factor)
    X = sp.Matrix([u, v, w]) / sp.sqrt(s)
    derivatives = [X.diff(t) for t in variables]
    symbolic_checks = {}

    def check(label, expression):
        residual = sp.factor(sp.cancel(expression))
        if residual != 0:
            residual = sp.simplify(residual)
        assert residual == 0, (label, residual)
        symbolic_checks[label] = True

    for i in range(2):
        for j in range(i, 2):
            check(f"metric_component_{i}_{j}", derivatives[i].dot(derivatives[j]) - g[i, j])
            check(f"second_form_component_{i}_{j}", X.dot(derivatives[i].diff(variables[j])) + g[i, j])
    check("determinant_is_s_inverse_cubed", g.det() - 1 / s ** 3)
    check("positive_oriented_area_density", derivatives[0].cross(derivatives[1]).dot(X) - s ** sp.Rational(-3, 2))

    # Derive the Christoffel symbols from the metric, rather than assuming K=1.
    gamma = [[[sp.factor(sum(
        ginv[k, ell] * (sp.diff(g[ell, j], variables[i])
                       + sp.diff(g[ell, i], variables[j])
                       - sp.diff(g[i, j], variables[ell])) / 2
        for ell in range(2))) for j in range(2)] for i in range(2)] for k in range(2)]
    expected_gamma = [[[-2 * p / s, -q / s], [-q / s, 0]],
                      [[0, -p / s], [-p / s, -2 * q / s]]]
    for k in range(2):
        for i in range(2):
            for j in range(2):
                check(f"christoffel_{k}_{i}_{j}", gamma[k][i][j] - expected_gamma[k][i][j])
    # Convention R(X,Y)Z = nabla_X nabla_Y Z - nabla_Y nabla_X Z.
    ruvv = [sp.diff(gamma[k][1][1], u) - sp.diff(gamma[k][0][1], v)
            + sum(gamma[m][1][1] * gamma[k][0][m]
                  - gamma[m][0][1] * gamma[k][1][m] for m in range(2))
            for k in range(2)]
    curvature = sp.factor(sum(g[0, k] * ruvv[k] for k in range(2)) / g.det())
    check("intrinsic_gaussian_curvature_is_one", curvature - 1)

    # A straight coordinate side is a reparametrized geodesic exactly when
    # its covariant acceleration is parallel to its coordinate velocity.
    for index, velocity in enumerate(((1, 0), (-1, 1), (0, -1))):
        acceleration = [sum(gamma[k][i][j] * velocity[i] * velocity[j]
                            for i in range(2) for j in range(2)) for k in range(2)]
        check(f"side_{index}_geodesic", velocity[0] * acceleration[1] - velocity[1] * acceleration[0])

    # Interior angles: inner products of the two outward rays are zero.
    corner_data = [((0, 0), (1, 0), (0, 1)),
                   ((1, 0), (-1, 0), (-1, 1)),
                   ((0, 1), (0, -1), (1, -1))]
    for index, (point, left, right) in enumerate(corner_data):
        gv = g.subs({u: point[0], v: point[1]})
        check(f"corner_{index}_orthogonal", (sp.Matrix(left).T * gv * sp.Matrix(right))[0])
        check(f"corner_{index}_left_unit", (sp.Matrix(left).T * gv * sp.Matrix(left))[0] - 1)
        check(f"corner_{index}_right_unit", (sp.Matrix(right).T * gv * sp.Matrix(right))[0] - 1)

    # Exact reduction of the area integral: the inner primitive and the
    # remaining derivative identity independently imply area = 2 atan(1).
    d = u * u + (1 - u) ** 2 / 2
    inner_primitive = (v - (1 - u) / 2) / (d * sp.sqrt(s))
    check("inner_area_antiderivative", sp.diff(inner_primitive, v) - s ** sp.Rational(-3, 2))
    q0 = u * u + (1 - u) ** 2
    inner_value = 2 * (1 - u) / ((2 * u * u + (1 - u) ** 2) * sp.sqrt(q0))
    check("inner_area_endpoints", inner_primitive.subs(v, 1 - u) - inner_primitive.subs(v, 0) - inner_value)
    z = u / sp.sqrt(q0)
    check("outer_area_antiderivative", 2 * sp.diff(z, u) / (1 + z * z) - inner_value)
    check("outer_substitution_left_endpoint", z.subs(u, 0))
    check("outer_substitution_right_endpoint", z.subs(u, 1) - 1)

    mp.mp.dps = dps
    density = lambda a, b: (a * a + b * b + (1 - a - b) ** 2) ** (-mp.mpf(3) / 2)
    direct_area = mp.quad(lambda a: mp.quad(lambda b: density(a, b), [0, 1 - a]), [0, mp.mpf("0.5"), 1])
    reduced_area = mp.quad(lambda a: 2 * (1 - a) / ((2 * a * a + (1 - a) ** 2)
                              * mp.sqrt(a * a + (1 - a) ** 2)), [0, mp.mpf("0.5"), 1])
    expected = mp.pi / 2
    residual = direct_area + 3 * mp.pi / 2 - 2 * mp.pi
    threshold = mp.power(10, -(dps - 10))
    assert abs(direct_area - expected) < threshold
    assert abs(reduced_area - expected) < threshold
    return {
        "map": "X(u,v) = (u,v,1-u-v)/sqrt(s), s=u^2+v^2+(1-u-v)^2",
        "domain": "u>=0, v>=0, u+v<=1",
        "positivity": "s>=1/3 on the domain, by 3*(u^2+v^2+w^2)>=(u+v+w)^2=1",
        "metric": {"E": "2/s-(u-w)^2/s^2", "F": "1/s-(u-w)*(v-w)/s^2", "G": "2/s-(v-w)^2/s^2"},
        "gaussian_curvature": "1",
        "area_and_curvature_density": "s^(-3/2)",
        "curvature_integral_exact_argument": "Integrate v explicitly; substitute z=u/sqrt(u^2+(1-u)^2) to obtain integral_0^1 2/(1+z^2) dz = pi/2",
        "curvature_integral": "pi/2",
        "edge_geodesic_curvature_integrals": ["0", "0", "0"],
        "interior_angles_over_pi": ["1/2", "1/2", "1/2"],
        "exterior_angles_over_pi": ["1/2", "1/2", "1/2"],
        "symbolic_checks": symbolic_checks,
        "numerical_diagnostics": {
            "working_decimal_digits": dps,
            "direct_2d_quadrature": mp.nstr(direct_area, dps),
            "reduced_1d_quadrature": mp.nstr(reduced_area, dps),
            "pi_over_two": mp.nstr(expected, dps),
            "observed_absolute_2d_difference": mp.nstr(abs(direct_area - expected), 12),
            "observed_absolute_1d_difference": mp.nstr(abs(reduced_area - expected), 12),
            "observed_gauss_bonnet_residual": mp.nstr(residual, 12),
            "caution": "Observed floating-point differences are diagnostics, not certified error bounds.",
        },
        "library_versions": {"sympy": sp.__version__, "mpmath": mp.__version__},
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path(__file__).resolve().parents[1] / "examples" / "smooth_results.json")
    parser.add_argument("--dps", type=int, default=50)
    args = parser.parse_args()
    if args.dps < 25:
        parser.error("--dps must be at least 25")
    results = {
        "status": "All diagnostic assertions passed",
        "scope": "Exact rational conformal example; finite symbolic spherical identities; uncertified high-precision quadrature",
        "formal_status": "No claim of Lean checking, iPRA derivability, or numerical interval certification is made by this script",
        "python_version": platform.python_version(),
        "conformal_triangle": conformal_example(),
        "spherical_octant": spherical_example(args.dps),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    print(f"PASS: conformal exact arithmetic and {len(results['spherical_octant']['symbolic_checks'])} spherical symbolic identities")
    print(f"Saved {args.output}")
    print("Observed spherical 2D quadrature difference:", results["spherical_octant"]["numerical_diagnostics"]["observed_absolute_2d_difference"])


if __name__ == "__main__":
    main()
