#!/usr/bin/env python3
"""Reference verification of the finite FTC and discrete Green identities.

All arithmetic is exact fractions. These executable checks cover finite
identities and explicit hypotheses, including sharp error examples. They do
not verify the analytic Taylor hypotheses and are not an iPRA formal proof.

Run: python3 tools/discrete_green.py
"""

from fractions import Fraction as Q
from math import factorial
import json


def ftc(values, derivatives, epsilon):
    """Shared values f_0,...,f_N; each Taylor residual <= h*epsilon."""
    n = len(derivatives)
    if n < 1 or len(values) != n + 1 or epsilon < 0:
        raise ValueError("bad finite FTC shape or tolerance")
    h = Q(1, n)
    residuals = [values[i + 1] - values[i] - h * derivatives[i] for i in range(n)]
    if any(abs(r) > h * epsilon for r in residuals):
        raise ValueError("FTC cell residual exceeds the supplied bound")
    defect = values[-1] - values[0] - h * sum(derivatives, Q(0))
    assert defect == sum(residuals, Q(0))
    assert abs(defect) <= epsilon
    return defect


def grid_shape(a, n):
    return len(a) == n + 1 and all(len(row) == n + 1 for row in a)


def boundary_sum(a, b, n):
    """CCW: bottom minus top, right minus left."""
    h = Q(1, n)
    return (h * sum((a[i][0] - a[i][n] for i in range(n)), Q(0))
            + h * sum((b[n][j] - b[0][j] for j in range(n)), Q(0)))


def discrete_green(a, b, db_du, da_dv, epsilon):
    """Verify the exact identity and |L - h^2 sum curl| <= 2 epsilon."""
    n = len(db_du)
    if (n < 1 or not grid_shape(a, n) or not grid_shape(b, n)
            or len(da_dv) != n or epsilon < 0
            or any(len(row) != n for row in db_du + da_dv)):
        raise ValueError("bad square-array shape or tolerance")
    h = Q(1, n)
    rb = [[b[i + 1][j] - b[i][j] - h * db_du[i][j]
           for j in range(n)] for i in range(n)]
    ra = [[a[i][j + 1] - a[i][j] - h * da_dv[i][j]
           for j in range(n)] for i in range(n)]
    if any(abs(r) > h * epsilon for table in (rb, ra) for row in table for r in row):
        raise ValueError("Green cell residual exceeds the supplied bound")
    L = boundary_sum(a, b, n)
    telescope = h * sum((b[i + 1][j] - b[i][j] - a[i][j + 1] + a[i][j]
                         for i in range(n) for j in range(n)), Q(0))
    curl_sum = h * h * sum((db_du[i][j] - da_dv[i][j]
                           for i in range(n) for j in range(n)), Q(0))
    residual_sum = h * sum((rb[i][j] - ra[i][j]
                            for i in range(n) for j in range(n)), Q(0))
    assert L == telescope
    assert L - curl_sum == residual_sum
    assert abs(L - curl_sum) <= 2 * epsilon
    return {"N": n, "boundary": str(L), "curl_sum": str(curl_sum),
            "defect": str(L - curl_sum), "bound": str(2 * epsilon)}


# Small exact polynomial operations. Keys are (x exponent, y exponent).
# Independent symbolic differentiation checks the pullback identity and a
# direct triangle Green calculation; these checks are not analytic axioms.
def clean(p):
    return {m: Q(c) for m, c in p.items() if c}


def add(p, q):
    r = dict(p)
    for m, c in q.items():
        r[m] = r.get(m, Q(0)) + c
    return clean(r)


def scale(c, p):
    return clean({m: c * v for m, v in p.items()})


def mul(p, q):
    r = {}
    for (i, j), c in p.items():
        for (k, l), d in q.items():
            m = (i + k, j + l)
            r[m] = r.get(m, Q(0)) + c * d
    return clean(r)


def power(p, k):
    r = {(0, 0): Q(1)}
    for _ in range(k):
        r = mul(r, p)
    return r


def derivative(p, axis):
    r = {}
    for (i, j), c in p.items():
        if axis == 0 and i:
            r[i - 1, j] = c * i
        if axis == 1 and j:
            r[i, j - 1] = c * j
    return clean(r)


def compose(p, x, y):
    r = {}
    for (i, j), c in p.items():
        r = add(r, scale(c, mul(power(x, i), power(y, j))))
    return r


def evaluate(p, x, y):
    return sum((c * x ** i * y ** j for (i, j), c in p.items()), Q(0))


def interval_integral(p):
    if any(j for i, j in p):
        raise ValueError("the edge pullback must depend only on the first variable")
    return sum((c / (i + 1) for (i, _), c in p.items()), Q(0))


def triangle_integral(p):
    return sum((c * Q(factorial(i) * factorial(j), factorial(i + j + 2))
                for (i, j), c in p.items()), Q(0))


def polynomial_green(p, q):
    one = {(0, 0): Q(1)}
    u = {(1, 0): Q(1)}
    v = {(0, 1): Q(1)}
    one_minus_u = add(one, scale(-1, u))
    # Phi(u,v) = (u,(1-u)v).
    y = mul(one_minus_u, v)
    pp, qq = compose(p, u, y), compose(q, u, y)
    a = add(pp, scale(-1, mul(v, qq)))
    b = mul(one_minus_u, qq)
    lhs = add(derivative(b, 0), scale(-1, derivative(a, 1)))
    curl = add(derivative(q, 0), scale(-1, derivative(p, 1)))
    rhs = mul(one_minus_u, compose(curl, u, y))
    assert lhs == rhs
    boundary = Q(0)
    for x_edge, y_edge in ((u, {}), (one_minus_u, u), ({}, one_minus_u)):
        integrand = add(mul(compose(p, x_edge, y_edge), derivative(x_edge, 0)),
                        mul(compose(q, x_edge, y_edge), derivative(y_edge, 0)))
        boundary += interval_integral(integrand)
    area = triangle_integral(curl)
    assert boundary == area
    return {"pullback_curl_identity": True, "boundary": str(boundary),
            "integral_Qx_minus_Py": str(area),
            "integral_Py_minus_Qx": str(-area)}


def self_check():
    out = {
        "status": "reference verification; not an iPRA formal proof",
        "arithmetic": "exact Fraction arithmetic and exact polynomial coefficients",
        "FTC": [], "Green_arbitrary_arrays": [], "Green_sharp_polynomial": [],
    }
    for n in (1, 2, 3, 7, 16):
        h = Q(1, n)
        eps = Q(3, 17)
        values = [Q((-1) ** i * (i + 1), i + 2) for i in range(n + 1)]
        # Derivative entries are arbitrary rational certificate data here.
        derivatives = [(values[i + 1] - values[i] - h * eps) / h for i in range(n)]
        defect = ftc(values, derivatives, eps)
        assert defect == eps  # sharp finite error example
        out["FTC"].append({"N": n, "defect": str(defect), "bound": str(eps)})
        a = [[Q((-1) ** (i + j) * (i + j + 1), i + 2 * j + 2)
              for j in range(n + 1)] for i in range(n + 1)]
        b = [[Q((i + 1) * (j + 2), 2 * i + j + 3)
              for j in range(n + 1)] for i in range(n + 1)]
        db = [[(b[i + 1][j] - b[i][j] - h * eps) / h
               for j in range(n)] for i in range(n)]
        da = [[(a[i][j + 1] - a[i][j] + h * eps) / h
               for j in range(n)] for i in range(n)]
        result = discrete_green(a, b, db, da, eps)
        assert Q(result["defect"]) == 2 * eps
        out["Green_arbitrary_arrays"].append(result)
        # A=-v^2, B=u^2 with genuine polynomial derivatives. Here eps=h,
        # and the finite estimate is attained: defect=2/N.
        a = [[-(j * h) ** 2 for j in range(n + 1)] for i in range(n + 1)]
        b = [[(i * h) ** 2 for j in range(n + 1)] for i in range(n + 1)]
        db = [[2 * i * h for j in range(n)] for i in range(n)]
        da = [[-2 * j * h for j in range(n)] for i in range(n)]
        result = discrete_green(a, b, db, da, h)
        assert Q(result["defect"]) == 2 * h
        out["Green_sharp_polynomial"].append(result)
    # Independent boundary/density rounding is sharp as well.
    n, eta, zeta = 5, Q(1, 101), Q(2, 103)
    h = Q(1, n)
    a = [[-(j * h) ** 2 for j in range(n + 1)] for i in range(n + 1)]
    b = [[(i * h) ** 2 for j in range(n + 1)] for i in range(n + 1)]
    rounded_a, rounded_b = [row[:] for row in a], [row[:] for row in b]
    for i in range(n):
        rounded_a[i][0] += eta
        rounded_a[i][n] -= eta
    for j in range(n):
        rounded_b[n][j] += eta
        rounded_b[0][j] -= eta
    rounded_curl = h * h * sum((2 * (i + j) * h - zeta
                                for i in range(n) for j in range(n)), Q(0))
    rounded_defect = boundary_sum(rounded_a, rounded_b, n) - rounded_curl
    assert rounded_defect == 2 * h + 4 * eta + zeta
    out["Green_rounding_sharp"] = {"N": n, "eta": str(eta), "zeta": str(zeta),
                                   "defect": str(rounded_defect),
                                   "bound_2eps_plus_4eta_plus_zeta": str(2 * h + 4 * eta + zeta)}
    ftc_eta = Q(1, 97)
    ftc_rounded_defect = (1 + ftc_eta) - (-ftc_eta) - (1 - ftc_eta)
    assert ftc_rounded_defect == 3 * ftc_eta
    out["FTC_rounding_sharp"] = {"defect": str(ftc_rounded_defect), "bound": str(3 * ftc_eta)}
    # Perturb every shared grid value by at most delta. Relative to exact
    # affine derivatives, each cell residual is at most 2 delta. This test
    # checks the explicit precision cost used to establish cell hypotheses.
    n, eps = 7, Q(1, 32)
    h = Q(1, n)
    delta = h * eps / 16
    a = [[Q(0) + (-1) ** (i + j) * delta for j in range(n + 1)]
         for i in range(n + 1)]
    b = [[i * h + (-1) ** (i + j + 1) * delta for j in range(n + 1)]
         for i in range(n + 1)]
    zeros = [[Q(0) for j in range(n)] for i in range(n)]
    ones = [[Q(1) for j in range(n)] for i in range(n)]
    result = discrete_green(a, b, ones, zeros, 2 * delta / h)
    assert 4 * n * delta == eps / 4
    out["shared_grid_auxiliary_precision"] = {
        "N": n, "delta": str(delta), "allowed_h_eps_over_16": str(h * eps / 16),
        "cell_bound": str(2 * delta), "aggregate_bound_4Ndelta": str(4 * n * delta),
        "actual_defect": result["defect"],
    }
    # A wrong orientation is observable even with zero cell residuals.
    n = 4
    h = Q(1, n)
    a = [[Q(0) for j in range(n + 1)] for i in range(n + 1)]
    b = [[i * h for j in range(n + 1)] for i in range(n + 1)]
    ones = [[Q(1) for j in range(n)] for i in range(n)]
    zeros = [[Q(0) for j in range(n)] for i in range(n)]
    correct = discrete_green(a, b, ones, zeros, Q(0))
    wrong_boundary = h * sum((b[0][j] - b[n][j] for j in range(n)), Q(0))
    wrong_defect = wrong_boundary - 1
    assert wrong_defect == -2 and abs(wrong_defect) > 0
    out["orientation_failure_detected"] = {
        "correct_boundary": correct["boundary"], "wrong_boundary": str(wrong_boundary),
        "wrong_defect": str(wrong_defect), "allowed_bound": "0", "detected": True,
    }
    try:
        discrete_green(a, b, zeros, zeros, Q(0))
    except ValueError as exc:
        out["false_cell_contract_rejected"] = str(exc)
    else:
        raise AssertionError("false Taylor contract was accepted")
    try:
        ftc([Q(0), Q(1)], [Q(0)], Q(0))
    except ValueError as exc:
        out["false_FTC_contract_rejected"] = str(exc)
    else:
        raise AssertionError("false FTC contract was accepted")
    pairs = [
        ({(2, 0): Q(1), (1, 1): Q(1), (0, 2): Q(2)},
         {(2, 0): Q(3), (1, 1): Q(1), (0, 2): Q(-1)}),
        ({(0, 3): Q(2, 7), (1, 0): Q(-3, 5)},
         {(3, 0): Q(4, 9), (1, 1): Q(5, 11)}),
        ({(0, 0): Q(3, 4), (2, 1): Q(-7, 3)},
         {(0, 0): Q(-2, 9), (1, 2): Q(11, 5)}),
    ]
    out["triangle_polynomial_pullback_and_Green"] = [polynomial_green(p, q) for p, q in pairs]
    assert out["triangle_polynomial_pullback_and_Green"][0]["boundary"] == "1/3"
    return out


if __name__ == "__main__":
    print(json.dumps(self_check(), indent=2, sort_keys=True))
