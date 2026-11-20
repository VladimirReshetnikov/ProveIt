"""Extract a scalar witness, including over real algebraic parameters.

The target formula is given by a suffix of quantifiers and a rational
polynomial Boolean matrix. Free parameters receive exact Scalar values.
Run this script to reproduce the examples in the report and README.
"""
from fractions import Fraction
import sympy as sp
from sympy.core.relational import Relational

from algebraic_roots import roots_over_scalars
from exact_scalars import Scalar
from quantifier_elimination import qe


def _specialize(expr, x, parameters):
    symbols = tuple(sorted(expr.free_symbols - {x}, key=sp.default_sort_key))
    missing = set(symbols) - parameters.keys()
    if missing:
        raise ValueError(f"give values for the parameters {sorted(map(str, missing))}")
    expression = sp.Poly(expr, x, *symbols, domain=sp.QQ)
    if expression.is_zero:
        return []
    coefficients = [Scalar.rational(0) for _ in range(expression.degree(x) + 1)]
    for (degree, *powers), c in expression.terms():
        value = Scalar.rational(Fraction(int(c.p), int(c.q)))
        for symbol, power in zip(symbols, powers):
            if power:
                value *= parameters[symbol] ** power
        coefficients[degree] += value
    while coefficients and coefficients[-1] == 0:
        coefficients.pop()
    return coefficients


def _sign_at(coeffs, point):
    value = Scalar.rational(0)
    for coefficient in reversed(coeffs):
        value = value * point + coefficient
    return value.sign()


def _cell_samples(roots):
    if not roots:
        yield Scalar.rational(0)
        return
    roots.sort()
    previous = roots[0]
    yield previous - 1
    yield previous
    for root in roots[1:]:
        if root != previous:
            yield (root + previous) / 2
            yield root
            previous = root
    yield previous + 1


def choose(variable, suffix, matrix, parameters=None):
    """Return x satisfying the quantified suffix, or None if no such x exists."""
    parameters = dict(parameters or {})
    if variable in parameters:
        raise ValueError("the chosen variable cannot also be a fixed parameter")
    if variable in [v for _, v in suffix]:
        raise ValueError("rename a bound occurrence shadowing the chosen variable")
    for key, value in parameters.items():
        if not isinstance(value, Scalar):
            parameters[key] = Scalar.rational(value)
    qf = qe(suffix, matrix)
    atoms = qf.atoms(Relational)
    coefficients = {a: _specialize(a.lhs-a.rhs, variable, parameters) for a in atoms}
    roots = []
    for coeffs in coefficients.values():
        if len(coeffs) > 1:
            roots.extend(roots_over_scalars(coeffs))
    for point in _cell_samples(roots):
        signs = {a: a.func(_sign_at(coeffs, point), 0) for a, coeffs in coefficients.items()}
        if bool(qf.xreplace(signs)):
            return point
    return None


def check_examples():
    x, y, a = sp.symbols("x y a", real=True)
    two = Scalar.rational(2)
    positive = choose(x, [], sp.And(sp.Eq(x**2, a), x > 0), {a: two.sqrt()})
    assert positive is not None and positive > 0 and positive**4 == 2
    assert choose(x, [], sp.Eq(x**2, a), {a: -two.sqrt()}) is None

    # Find an x satisfying forall y, y^2 != x. Every valid answer is negative.
    fails_square = choose(x, [("forall", y)], sp.Ne(y*y, x))
    assert fails_square is not None and fails_square < 0

    # Equilateral triangle above the unit segment: choose the two coordinates.
    triangle = sp.And(sp.Eq(x*x+y*y, 1), sp.Eq((x-1)**2+y*y, 1), y > 0)
    # Solve the equivalent difference equation first to expose the simple guard.
    reduced = sp.And(sp.Eq(2*x, 1), sp.Eq(y*y, 1-x*x), y > 0)
    px = choose(x, [("exists", y)], reduced)
    assert px == Fraction(1, 2)
    py = choose(y, [], triangle, {x: px})
    assert 2*py == Scalar.rational(3).sqrt()
    print("Passed: fourth-root witness with an algebraic parameter, empty fiber, "
          "quantified counterexample and positive equilateral vertex.")


if __name__ == "__main__":
    check_examples()
