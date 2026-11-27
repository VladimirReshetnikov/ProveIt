"""Exact rational Hermite error-locator demonstration (SymPy >= 1.10).

An observed monic polynomial represents a multiset of algebraic nodes.
Vanishing at them, including all listed jets, is divisibility by this
polynomial. This permits exact tests without isolating algebraic numbers.
"""
import json

import sympy as sp

x = sp.Symbol("x")
ring = lambda expr: sp.Poly(expr, x, domain=sp.QQ)


def polynomial_with_roots(roots):
    return ring(sp.prod(x - root for root in roots))


def solve_locator(observed, columns, error_budget):
    # The distinguished column has a monic locator; the others are unrestricted.
    basis = []
    unknowns = []
    for i, col in enumerate(columns):
        count = error_budget if i == 0 else error_budget + 1
        for j in range(count):
            basis.append((ring(x**j) * col).rem(observed))
            unknowns.append((i, j))
    rhs = -(ring(x**error_budget) * columns[0]).rem(observed)
    matrix = sp.Matrix([[pol.nth(i) for pol in basis] for i in range(observed.degree())])
    target = sp.Matrix([rhs.nth(i) for i in range(observed.degree())])
    solution, params = matrix.gauss_jordan_solve(target)
    assert params.rows == 0
    polynomials = [ring(x**error_budget)] + [ring(0) for _ in columns[1:]]
    for (col, j), entry in zip(unknowns, solution):
        polynomials[col] += ring(entry * x**j)
    return polynomials, matrix.rank()


def main():
    f1 = polynomial_with_roots([-9, -7, -5, -3, -1, -1, 1, 1, 3, 5, 7, 9])
    f2 = polynomial_with_roots([-10, -8, -6, -4, -2, -1, 1, 2, 4, 6, 8, 10])
    columns = [f1.diff()*f2.diff(), f1.diff()*f2, f1*f2.diff(), f1*f2]
    # A = [[2, 1], [1, 3]]. The column order is both, first, second, neither.
    expected = [1, 3, 2, 5]
    characteristic = sum((v*col for v, col in zip(expected, columns)), ring(0))
    assert characteristic.eval(1) == characteristic.eval(-1) == 0
    assert characteristic.diff().eval(-1) != 0
    assert characteristic.eval(0)*characteristic.eval(87) != 0
    genuine = characteristic.exquo(ring(x-1))
    # The extra -1 inflates a genuine multiplicity. 0 and 87 are spurious nodes.
    true_locator = polynomial_with_roots([-1, 0, 87])
    observed = (genuine*true_locator).monic()
    recovered, rank = solve_locator(observed, columns, 3)
    locator = recovered[0]
    assert locator == true_locator
    decoded = [pol.exquo(locator) for pol in recovered]
    assert decoded == [ring(v) for v in expected]
    reconstructed = sum((v*col for v, col in zip(recovered, columns)), ring(0))
    assert reconstructed.rem(observed).is_zero
    print(json.dumps({
        "arithmetic": "exact rationals; polynomial surrogate",
        "true_degree": characteristic.degree(), "erased_copies": [1],
        "false_copies": [-1, 0, 87], "inflated_true_location": -1,
        "observed_degree": observed.degree(), "affine_system_rank": rank,
        "locator": str(locator.as_expr()),
        "decoded_coefficients_both_first_second_neither": expected,
        "jet_divisibility_verified": True
    }, indent=2))


if __name__ == "__main__":
    main()
