#!/usr/bin/env python3
"""Exact finite checks for the surreal vector/tensor article.

Run from the article directory:
    python3 code/verify.py

Requires Python >= 3.10 and SymPy. No numerical approximations, network access,
external data, or files are used. These finite algebraic checks are not proofs
of the article's infinite-support, smooth-prolongation, or existence theorems.
"""
from __future__ import annotations

from fractions import Fraction
from itertools import combinations, product
from math import prod
import platform
import sys
from typing import Callable

try:
    import sympy as sp
except ImportError as exc:
    raise SystemExit("SymPy is required. Install it with: python3 -m pip install sympy") from exc

Expr = sp.Expr
Form = dict[tuple[int, ...], Expr]
Fourier = dict[int, Fraction]
CHECKS = 0


def equal(actual: Expr, expected: Expr, label: str) -> None:
    """Require exact symbolic equality; a failure names the tested identity."""
    global CHECKS
    difference = sp.simplify(sp.expand(actual - expected))
    if difference != 0:
        raise AssertionError(f"{label}: nonzero difference {difference}")
    CHECKS += 1


def clean(form: Form) -> Form:
    return {key: sp.expand(value) for key, value in form.items() if sp.expand(value) != 0}


def form_add(*forms: Form) -> Form:
    result: Form = {}
    for form in forms:
        for index, coefficient in form.items():
            result[index] = result.get(index, sp.S.Zero) + coefficient
    return clean(result)


def d(form: Form, coordinates: tuple[Expr, ...]) -> Form:
    """Exterior derivative in an increasing-index basis."""
    result: Form = {}
    for index, coefficient in form.items():
        for j, coordinate in enumerate(coordinates):
            if j in index:
                continue
            sign = (-1) ** sum(i < j for i in index)
            target = tuple(sorted((j,) + index))
            result[target] = result.get(target, sp.S.Zero) + sign * sp.diff(coefficient, coordinate)
    return clean(result)


def contract(form: Form, vector: tuple[Expr, ...]) -> Form:
    result: Form = {}
    for index, coefficient in form.items():
        for position, j in enumerate(index):
            target = index[:position] + index[position + 1:]
            result[target] = result.get(target, sp.S.Zero) + (-1) ** position * vector[j] * coefficient
    return clean(result)


def form_equal(actual: Form, expected: Form, label: str) -> None:
    for index in sorted(actual.keys() | expected.keys()):
        equal(actual.get(index, sp.S.Zero), expected.get(index, sp.S.Zero), f"{label}, index {index}")
    if not actual and not expected:
        equal(sp.S.Zero, sp.S.Zero, label)


def radial_homotopy(form: Form, coordinates: tuple[Expr, ...]) -> Form:
    """H on a degree-p monomial of coefficient degree m: i_E/(m+p)."""
    result: Form = {}
    for index, coefficient in form.items():
        p = len(index)
        if p == 0:
            continue
        for powers, scalar in sp.Poly(coefficient, *coordinates).terms():
            monomial = scalar * prod(x ** a for x, a in zip(coordinates, powers))
            denominator = sum(powers) + p
            result = form_add(result, contract({index: monomial / denominator}, coordinates))
    return clean(result)


def test_warped_geometry() -> None:
    x, y, z = sp.symbols("x y z", real=True)
    epsilon = sp.symbols("epsilon", positive=True)
    coordinates = (x, y, z)
    n = len(coordinates)
    metric = sp.diag(1, x*x + epsilon*epsilon, 1)
    inverse = metric.inv()
    gamma = [[[sp.simplify(sum(
        inverse[a, ell] * (sp.diff(metric[ell, j], coordinates[i])
                          + sp.diff(metric[ell, i], coordinates[j])
                          - sp.diff(metric[i, j], coordinates[ell]))
        for ell in range(n)) / 2) for j in range(n)] for i in range(n)] for a in range(n)]
    # R^ell_{k i j}: R(D_i,D_j)D_k, matching the article's convention.
    def curvature(ell: int, k: int, i: int, j: int) -> Expr:
        return sp.simplify(
            sp.diff(gamma[ell][j][k], coordinates[i])
            - sp.diff(gamma[ell][i][k], coordinates[j])
            + sum(gamma[ell][i][a] * gamma[a][j][k]
                  - gamma[ell][j][a] * gamma[a][i][k] for a in range(n)))
    expected_gamma = {
        (0, 1, 1): -x,
        (1, 0, 1): x / (x*x + epsilon*epsilon),
        (1, 1, 0): x / (x*x + epsilon*epsilon),
    }
    for a, i, j in product(range(n), repeat=3):
        equal(gamma[a][i][j], expected_gamma.get((a, i, j), sp.S.Zero), f"Christoffel {a,i,j}")
    ricci = sp.Matrix(n, n, lambda k, j: sum(curvature(i, k, i, j) for i in range(n)))
    scalar = sp.simplify(sum(inverse[k, j] * ricci[k, j] for k, j in product(range(n), repeat=2)))
    sectional = sp.simplify(curvature(0, 1, 0, 1) / metric[1, 1])
    equal(sectional, -epsilon**2 / (x*x + epsilon*epsilon)**2, "sectional curvature")
    equal(scalar, -2*epsilon**2 / (x*x + epsilon*epsilon)**2, "scalar curvature")
    equal(scalar.subs(x, 0), -2/epsilon**2, "curvature at the narrow scale")
    print(f"  sectional curvature = {sectional}")
    print(f"  scalar curvature = {scalar}")


def test_metric_inverse() -> None:
    epsilon = sp.symbols("epsilon")
    a, b, c, x = sp.symbols("a b c x")
    g0 = sp.Matrix([[2, 1], [1, 3]])
    h = sp.Matrix([[a*x, b], [b, c*x*x]])
    g0_inv = g0.inv()
    first_inverse = g0_inv - epsilon * g0_inv * h * g0_inv
    defect = (g0 + epsilon * h) * first_inverse - sp.eye(2)
    for i, j in product(range(2), repeat=2):
        polynomial = sp.Poly(sp.expand(defect[i, j]), epsilon)
        equal(polynomial.nth(0), sp.S.Zero, f"inverse constant coefficient {i,j}")
        equal(polynomial.nth(1), sp.S.Zero, f"inverse linear coefficient {i,j}")
        equal(polynomial.nth(2), -(h * g0_inv * h * g0_inv)[i, j], f"inverse quadratic defect {i,j}")


def test_lie_jacobi() -> None:
    x = sp.symbols("x0:4")
    epsilon = sp.symbols("epsilon")
    X = (x[1] + epsilon*x[0], x[2]*x[0], x[3], x[0]*x[1])
    Y = (x[2], x[3] + x[0]*x[0], epsilon*x[1], x[2]*x[3])
    Z = (x[0]*x[3], x[1], x[0] + x[1]*x[3], epsilon*x[2])
    def bracket(A: tuple[Expr, ...], B: tuple[Expr, ...]) -> tuple[Expr, ...]:
        return tuple(sp.expand(sum(A[j]*sp.diff(B[i], x[j]) - B[j]*sp.diff(A[i], x[j])
                                   for j in range(4))) for i in range(4))
    terms = (bracket(X, bracket(Y, Z)), bracket(Y, bracket(Z, X)), bracket(Z, bracket(X, Y)))
    for i in range(4):
        equal(sum(term[i] for term in terms), sp.S.Zero, f"Jacobi component {i}")


def test_exterior_derivative() -> None:
    x = sp.symbols("x0:4")
    epsilon = sp.symbols("epsilon")
    two_form = {(0, 1): x[0]*x[2]**2 + epsilon*x[3],
                (0, 3): x[1]*x[2]*x[3],
                (1, 2): x[0]**2*x[3] + epsilon*x[1]*x[2],
                (2, 3): x[0]*x[1]**3}
    form_equal(d(d(two_form, x), x), {}, "d squared on a 2-form")
    one_form = {(i,): x[(i + 1) % 4]**2*x[(i + 2) % 4] for i in range(4)}
    form_equal(d(d(one_form, x), x), {}, "d squared on a 1-form")


def test_hodge_signs() -> None:
    tested = 0
    for n in range(1, 7):
        for signs in product((-1, 1), repeat=n):
            q = sum(sign < 0 for sign in signs)
            def star_basis(index: tuple[int, ...]) -> tuple[int, tuple[int, ...]]:
                complement = tuple(i for i in range(n) if i not in index)
                concatenation = index + complement
                inversions = sum(concatenation[i] > concatenation[j]
                                 for i in range(n) for j in range(i + 1, n))
                return (-1)**inversions * prod(signs[i] for i in index), complement
            for p in range(n + 1):
                for index in combinations(range(n), p):
                    first_sign, complement = star_basis(index)
                    second_sign, original = star_basis(complement)
                    if original != index:
                        raise AssertionError("Hodge star changed the basis after squaring")
                    equal(sp.Integer(first_sign * second_sign), sp.Integer((-1)**(p*(n-p)+q)),
                          f"Hodge square n={n}, signature={signs}, index={index}")
                    tested += 1
    print(f"  checked {tested} basis/signature combinations, dimensions 1 through 6")


def test_radial_homotopy() -> None:
    x = sp.symbols("x0:4")
    for p in range(5):
        form: Form = {}
        for serial, index in enumerate(combinations(range(4), p)):
            form[index] = (serial + 1)*x[0]**2*x[2] + x[1]*x[3]**3 + 2
        result = form_add(d(radial_homotopy(form, x), x), radial_homotopy(d(form, x), x))
        expected = form
        if p == 0:
            expected = {(): form[()] - form[()].subs({v: 0 for v in x})}
        form_equal(result, expected, f"radial homotopy, degree {p}")


def fourier_add(*series: Fourier) -> Fourier:
    out: Fourier = {}
    for current in series:
        for k, coefficient in current.items():
            out[k] = out.get(k, Fraction(0)) + coefficient
    return {k: coefficient for k, coefficient in out.items() if coefficient}


def convolve(a: Fourier, b: Fourier) -> Fourier:
    out: Fourier = {}
    for k, ak in a.items():
        for ell, bell in b.items():
            out[k + ell] = out.get(k + ell, Fraction(0)) + ak * bell
    return {k: coefficient for k, coefficient in out.items() if coefficient}


def test_nonlinear_pde() -> None:
    global CHECKS
    u: dict[int, Fourier] = {1: {-1: Fraction(1, 4), 1: Fraction(1, 4)}}
    force = {-1: Fraction(1, 2), 1: Fraction(1, 2)}
    for m in range(2, 7):
        source = fourier_add(*(convolve(u[a], u[m-a]) for a in range(1, m)))
        u[m] = {k: -coefficient / (1 + k*k) for k, coefficient in source.items()}
    expected = {
        1: {-1: Fraction(1, 4), 1: Fraction(1, 4)},
        2: {0: Fraction(-1, 8), -2: Fraction(-1, 80), 2: Fraction(-1, 80)},
        3: {-1: Fraction(11, 320), 1: Fraction(11, 320),
            -3: Fraction(1, 1600), 3: Fraction(1, 1600)},
    }
    for m in range(1, 4):
        if u[m] != expected[m]:
            raise AssertionError(f"Displayed PDE coefficient u_{m} does not match {u[m]}")
        CHECKS += 1
    for m in range(1, 7):
        linear = {k: (1 + k*k)*coefficient for k, coefficient in u[m].items()}
        quadratic = fourier_add(*(convolve(u[a], u[m-a]) for a in range(1, m)))
        residual = fourier_add(linear, quadratic,
                               {k: -v for k, v in force.items()} if m == 1 else {})
        if residual:
            raise AssertionError(f"Nonzero PDE residual at order {m}: {residual}")
        CHECKS += 1
        # All data are real and even, so report the real cosine coefficients.
        if any(u[m].get(-k, Fraction(0)) != value for k, value in u[m].items()):
            raise AssertionError("Expected real even Fourier series")
        terms = []
        if 0 in u[m]:
            terms.append(str(u[m][0]))
        terms.extend(f"({2*u[m][k]}) cos({k} x1)" for k in sorted(u[m]) if k > 0)
        print(f"  u_{m} = " + " + ".join(terms))
    print("  coefficients of epsilon^1 through epsilon^6 in the PDE residual vanish exactly")


def main() -> int:
    print("Exact finite verification: Vector and Tensor Fields over the Surreal Numbers")
    print(f"Python {platform.python_version()}; SymPy {sp.__version__}")
    print("Only finite algebraic examples are checked; no claim of formal proof checking.\n")
    tests: tuple[tuple[str, Callable[[], None]], ...] = (
        ("Warped metric, Christoffel symbols, Ricci and scalar curvature", test_warped_geometry),
        ("First-order metric inverse and its exact quadratic defect", test_metric_inverse),
        ("Polynomial vector-field Jacobi identity", test_lie_jacobi),
        ("Exterior derivative squared", test_exterior_derivative),
        ("Hodge star squared for every diagonal sign assignment", test_hodge_signs),
        ("Polynomial radial homotopy in degrees 0 through 4", test_radial_homotopy),
        ("Six orders of the nonlinear periodic PDE solution", test_nonlinear_pde),
    )
    for name, test in tests:
        print(name)
        before = CHECKS
        test()
        print(f"PASS ({CHECKS-before} exact assertions)\n")
    print(f"ALL {len(tests)} CHECK GROUPS PASSED; {CHECKS} exact assertions.")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except AssertionError as exc:
        print(f"VERIFICATION FAILED: {exc}", file=sys.stderr)
        raise SystemExit(1) from exc
