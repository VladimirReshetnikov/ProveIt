#!/usr/bin/env python3
"""Exact finite checks for Report153; Python >=3.10, standard library only.

This companion verifies rational algebra and finite enumerations. It does not
prove asymptotic remainders, transfer theorems, inverse rounding thresholds, or
novelty. The two coefficient constructions have distinct mathematical routes.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as Q
from math import factorial
from pathlib import Path
import sys

from safe_io import (ROOT, RESULTS, VerificationError, encoded_json, exact_equal,
                     load_json, require, write_new_json)

ORDER = 7


def rational(value):
    return str(Q(value))


class Series:
    """Dense truncated ordinary series over the rational numbers."""
    def __init__(self, degree):
        require(type(degree) is int and degree >= 0, "Invalid series degree")
        self.degree = degree

    def pad(self, a):
        return (list(map(Q, a)) + [Q(0)] * (self.degree + 1))[:self.degree + 1]

    def add(self, a, b):
        return [x + y for x, y in zip(self.pad(a), self.pad(b))]

    def scale(self, a, value):
        return [Q(value) * x for x in self.pad(a)]

    def mul(self, a, b):
        a, b = self.pad(a), self.pad(b)
        result = self.pad([])
        for i, x in enumerate(a):
            if x:
                for j in range(self.degree + 1 - i):
                    result[i + j] += x * b[j]
        return result

    def power(self, a, exponent):
        require(type(exponent) is int and exponent >= 0, "Invalid series exponent")
        result = self.pad([1])
        for _ in range(exponent):
            result = self.mul(result, a)
        return result

    def reciprocal(self, a):
        a = self.pad(a)
        require(a[0] != 0, "Reciprocal requires a nonzero constant term")
        result = self.pad([1 / a[0]])
        for n in range(1, self.degree + 1):
            result[n] = -sum((a[i] * result[n-i] for i in range(1, n+1)), Q(0)) / a[0]
        return result

    def compose(self, outer, inner):
        inner = self.pad(inner)
        require(inner[0] == 0, "Formal composition requires zero inner constant")
        result = self.pad([])
        for value in reversed(self.pad(outer)):
            result = self.mul(result, inner)
            result[0] += value
        return result

    def derivative(self, a):
        return self.pad([i * Q(a[i]) for i in range(1, len(a))])

    def exp_zero(self, a):
        a = self.pad(a)
        require(a[0] == 0, "Rational exponential requires zero constant")
        result = self.pad([1])
        for n in range(1, self.degree + 1):
            result[n] = sum((i*a[i]*result[n-i] for i in range(1, n+1)), Q(0)) / n
        return result

    def log_one(self, a):
        a = self.pad(a)
        require(a[0] == 1, "Formal logarithm requires constant one")
        logarithmic_derivative = self.mul(self.derivative(a), self.reciprocal(a))
        return self.pad([0] + [logarithmic_derivative[n-1] / n
                               for n in range(1, self.degree+1)])


def validate_inputs(data):
    require(isinstance(data, dict), "Inputs must be a JSON object")
    exact_equal(data.get("schema"), "report153-exact-inputs-v1", "Input schema")
    rows = data.get("rows")
    require(isinstance(rows, list) and len(rows) == 9, "Exactly nine input rows required")
    for n, row in enumerate(rows, 1):
        require(isinstance(row, dict) and set(row) == {"n", "a", "r"}, "Invalid input row keys")
        require(all(type(row[key]) is int and row[key] > 0 for key in row),
                "Input n, a and r must be positive integers, not booleans")
        exact_equal(row["n"], n, "Input row order")
    return rows


def load_claims(path):
    claims = load_json(path)
    require(isinstance(claims, dict), "Claims must be a JSON object")
    require(all(isinstance(k, str) and isinstance(v, str) for k, v in claims.items()),
            "Every claim must have a string key and a rational string value")
    for key, value in claims.items():
        exact_equal(rational(value), value, f"Canonical rational claim {key}")
    return claims


def direct_coefficients(rows, order=ORDER):
    """Solve F(Q)=A recursively, then construct H directly.

    F(x)=sum_{n>=1} n!x^n, Q=T(A), C=sum r_{d+1}x^d, and
    H=C*Q'/((Q/x)*A')*exp((1-1/(Q/x))/x).
    This follows the original recursive-Q calculation, rewritten without SymPy.
    """
    require(0 <= order <= ORDER, "Only orders through h7 are supported by fixed inputs")
    degree = order + 2
    s = Series(degree)
    A = s.pad([0] + [row["a"] for row in rows[:degree]])
    C = s.pad([row["r"] for row in rows[:order+1]])
    exact_equal(A[1], Q(1), "A linear normalization")
    q = s.pad([0, 1])
    for n in range(2, degree + 1):
        # At degree n, all nonlinear powers depend only on previously found q_j.
        nonlinear = sum((factorial(j)*s.power(q, j)[n] for j in range(2, n+1)), Q(0))
        q[n] = A[n] - nonlinear
    Fq = s.compose([0] + [factorial(j) for j in range(1, degree+1)], q)
    exact_equal(Fq, A, "Recursive Q reversion residual F(Q)-A")
    exact_equal(q[2], Q(0), "Q=x+O(x^3)")
    qbar_inv = s.reciprocal(q[1:])
    exponent = s.pad([-qbar_inv[k+1] for k in range(order+1)])
    exact_equal(exponent[0], Q(0), "H exponent constant")
    prefactor = s.mul(s.mul(C, s.derivative(q)),
                      s.mul(qbar_inv, s.reciprocal(s.derivative(A))))
    h = s.mul(prefactor, s.exp_zero(exponent))[:order+1]
    for name, values in (("Q", q), ("H exponent", exponent[:order+1]),
                         ("H prefactor", prefactor[:order+1])):
        require(all(v.denominator == 1 for v in values), f"{name} must be integral")
    require(all((factorial(k)*v).denominator == 1 for k, v in enumerate(h)),
            "Denominator bound k! h_k integral")
    return h, {"Q": list(map(rational, q)),
               "prefactor": list(map(rational, prefactor[:order+1])),
               "exponent": list(map(rational, exponent[:order+1])),
               "factorial_scaled_h": [int(factorial(k)*v) for k, v in enumerate(h)],
               "reversion_residual": list(map(rational, s.add(Fq, s.scale(A, -1))))}


def independent_coefficients(rows, order=ORDER):
    """Lagrange inversion and finite-polynomial transfer, not recursive Q.

    t_n=(1/n)[z^(n-1)](z/F(z))^n. First construct exp(2)*D_S using
    T, then compose with each B_R and multiply by its finite context C_R.
    The constants -2 and +2 of the two exponents cancel exactly. This route
    adapts the independently authored coefficient verification implementation.
    """
    degree = order + 2
    s = Series(degree)
    inverse_fbar = s.reciprocal([factorial(j+1) for j in range(degree+1)])
    T = s.pad([0] + [s.power(inverse_fbar, n)[n-1] / n
                     for n in range(1, degree+1)])
    identity = s.compose([0]+[factorial(j) for j in range(1, degree+1)], T)
    exact_equal(identity, s.pad([0, 1]), "Lagrange reversion residual F(T)-x")
    tbar_inverse = s.reciprocal(T[1:])
    Et = s.pad([-v for v in tbar_inverse[1:]])
    exact_equal(Et[0], Q(-2), "Simple-series exponential constant")
    Et[0] = Q(0)  # exp(-2) is canceled by exp(+2) in the finite transfer.
    simple_normalized = s.mul(s.mul(s.derivative(T), tbar_inverse), s.exp_zero(Et))
    A = [0] + [row["a"] for row in rows]
    C = [row["r"] for row in rows]
    transfers = []
    for R in range(1, order+2):
        B = s.pad(A[:R+2])
        ctx = s.pad(C[:R])
        bbar_inverse = s.reciprocal(B[1:])
        Eb = s.pad([-v for v in bbar_inverse[1:]])
        exact_equal(Eb[0], Q(2), f"Finite B_{R} exponential constant")
        Eb[0] = Q(0)
        result = s.mul(s.mul(s.mul(ctx, bbar_inverse), s.exp_zero(Eb)),
                       s.compose(simple_normalized, B))[:R]
        transfers.append({"R": R, "coefficients": list(map(rational, result))})
    return [Q(x) for x in transfers[-1]["coefficients"]], {
        "T_lagrange": list(map(rational, T)),
        "exp2_D_simple": list(map(rational, simple_normalized[:order+1])),
        "finite_polynomial_stabilization": transfers}


def bernoulli_numbers(maximum):
    """Exact triangular recurrence, with B_1=-1/2."""
    from math import comb
    values = [Q(1)]
    for n in range(1, maximum+1):
        values.append(-sum((Q(comb(n+1, k))*values[k] for k in range(n)), Q(0)) / (n+1))
    return values


def factorial_to_ordinary(h, degree=None):
    """Convert known falling-factorial coefficients to ordinary inverse powers."""
    s = Series(len(h)-1 if degree is None else degree)
    U = s.pad([])
    for k, value in enumerate(h):
        denominator = s.pad([1])
        for j in range(k):
            denominator = s.mul(denominator, [1, -j])
        term = [0]*k + s.reciprocal(denominator)
        U = s.add(U, s.scale(term, value))
    return U


def logarithm_checks(h):
    """Convert falling-factorial coefficients to inverse powers, then log."""
    s = Series(len(h)-1)
    U = factorial_to_ordinary(h)
    log_U = s.log_one(U)
    # A second logarithm construction, from the finite log(1+v) power sum.
    v = U.copy()
    v[0] -= 1
    alternative = s.pad([])
    for k in range(1, s.degree+1):
        alternative = s.add(alternative, s.scale(s.power(v, k), Q((-1)**(k+1), k)))
    exact_equal(log_U, alternative, "Independent formal-log construction")
    B = bernoulli_numbers(s.degree+1)
    correction = log_U.copy()
    stirling = s.pad([])
    for power in range(1, s.degree+1, 2):
        stirling[power] = B[power+1] / ((power+1)*power)
        correction[power] += stirling[power]
    return U, correction, {"ordinary_inverse_powers": list(map(rational, U)),
                          "log_U": list(map(rational, log_U)),
                          "stirling_correction": list(map(rational, stirling)),
                          "log_a_inverse_powers": list(map(rational, correction)),
                          "logarithm_route_residual": list(map(rational, s.add(log_U, s.scale(alternative, -1))))}


class Laurent:
    """Rational Laurent polynomials in formal D and C, for inverse residuals."""
    def __init__(self, terms=None):
        self.terms = {k: Q(v) for k, v in (terms or {}).items() if v}

    @staticmethod
    def coerce(value):
        return value if isinstance(value, Laurent) else Laurent({(0, 0): value})

    def __add__(self, other):
        terms = self.terms.copy()
        for key, value in self.coerce(other).terms.items():
            terms[key] = terms.get(key, Q(0)) + value
        return Laurent(terms)

    __radd__ = __add__

    def __neg__(self):
        return Laurent({key: -value for key, value in self.terms.items()})

    def __sub__(self, other):
        return self + -self.coerce(other)

    def __rsub__(self, other):
        return self.coerce(other) + -self

    def __mul__(self, other):
        terms = {}
        for (i, j), value in self.terms.items():
            for (k, ell), coefficient in self.coerce(other).terms.items():
                key = (i+k, j+ell)
                terms[key] = terms.get(key, Q(0)) + value*coefficient
        return Laurent(terms)

    __rmul__ = __mul__

    def __truediv__(self, scalar):
        return self * (Q(1)/scalar)

    def __pow__(self, exponent):
        require(type(exponent) is int and exponent >= 0, "Invalid Laurent exponent")
        result = Laurent.coerce(1)
        for _ in range(exponent):
            result = result*self
        return result

    def encoded(self):
        return {f"{i},{j}": rational(value) for (i, j), value in sorted(self.terms.items())}


def inverse_checks(log_coefficients):
    """Cancel the constant and 1/u residuals, with L=log X and D=log u.

    n(log n-1)+D_n/2+C+b1/n+b2/n^2 is expanded at
    n=u+d0+d1/u, where u(log u-1)=L and D_n=log n.
    The remaining 1/u^2 coefficient is reported, not claimed to vanish.
    """
    D, C, Di = Laurent({(1, 0): 1}), Laurent({(0, 1): 1}), Laurent({(-1, 0): 1})
    b1, b2 = log_coefficients[1:3]
    d0 = -Q(1, 2)-C*Di
    universal_numerator = Q(1, 8)-b1
    d1 = universal_numerator*Di-C*C*Di**3/2
    residual0 = D*d0+D/2+C
    residual_after_first_shift = d0*d0/2+d0/2+b1
    residual1 = D*d1+residual_after_first_shift
    residual2 = d0*d1-d0**3/6+d1/2-d0*d0/4-b1*d0+b2
    exact_equal(residual0.encoded(), {}, "Inverse constant residual")
    exact_equal(residual1.encoded(), {}, "Inverse second-shift 1/u residual")
    return universal_numerator, {"variables": ["D=log(u)", "C=log(2*pi)/2-log(4)"],
                                "encoding": "key i,j means coefficient of D^i C^j",
                                "delta0": d0.encoded(), "delta1": d1.encoded(),
                                "constant_residual": residual0.encoded(),
                                "first_shift_1_over_u_residual": residual_after_first_shift.encoded(),
                                "second_shift_1_over_u_residual": residual1.encoded(),
                                "second_shift_1_over_u_squared_residual": residual2.encoded()}


def validate_sampling_inputs(data):
    rows = data.get("sampling_rows")
    require(isinstance(rows, list) and len(rows) == 8, "Exactly eight sampling input rows required")
    for n, row in enumerate(rows, 1):
        require(isinstance(row, dict) and set(row) == {"n", "b", "c"}, "Invalid sampling input keys")
        require(all(type(row[key]) is int for key in row), "Sampling input counts must be integers")
        require(row["b"] > 0 and row["c"] >= 0, "Invalid sampling input count")
        exact_equal(row["n"], n, "Sampling input row order")
    return rows


def sampling_algebra_checks(sampling_rows, h):
    """Construct H4 two ways and TV=V*(1/U-1) to degree seven.

    Only g0..g6 are known or used: the second factor has constant zero, so its
    degree-seven product does not depend on the unspecified g7 or v7.
    """
    context_rows = [{"n": row["n"], "a": row["b"], "r": row["c"]}
                    for row in sampling_rows]
    g, direct = direct_coefficients(context_rows, 6)
    other, independent = independent_coefficients(context_rows, 6)
    exact_equal(g, other, "H4 direct versus independent finite-transfer route")
    for row in independent["finite_polynomial_stabilization"]:
        exact_equal(row["coefficients"], list(map(rational, g[:row["R"]])),
                    f"H4 finite stabilization R={row['R']}")
    U = factorial_to_ordinary(h)
    V = factorial_to_ordinary(g)
    s = Series(7)
    W = s.reciprocal(U)
    W[0] -= 1
    exact_equal(W[0], Q(0), "TV inverse factor constant")
    tv = s.mul(V, W)
    # Independently solve U*TV=V*(1-U), avoiding the reciprocal route.
    one_minus_U = s.scale(U, -1)
    one_minus_U[0] += 1
    numerator = s.mul(V, one_minus_U)
    alternative = s.pad([])
    for n in range(1, 8):
        alternative[n] = numerator[n]-sum((U[k]*alternative[n-k] for k in range(1, n+1)), Q(0))
    exact_equal(tv, alternative, "TV product versus quotient recurrence")
    # The unknown next V coefficient is annihilated at the checked precision.
    changed_V = V + [Q(123456789)]
    exact_equal(s.mul(changed_V, W), tv, "TV independence from unknown v7")
    claims = {f"b{row['n']}": str(row["b"]) for row in sampling_rows}
    claims.update({f"c{row['n']}": str(row["c"]) for row in sampling_rows})
    claims.update({f"g{k}": rational(value) for k, value in enumerate(g)})
    claims.update({f"v{k}": rational(value) for k, value in enumerate(V)})
    claims.update({f"tv{k}": rational(value) for k, value in enumerate(tv) if k})
    return claims, {"H4_direct_recursive_Q": direct,
                    "H4_independent_lagrange_transfer": independent,
                    "H4_inverse_factorial_coefficients": list(map(rational, g)),
                    "M4_ordinary_coefficients_through_degree6": list(map(rational, V)),
                    "TV_coefficients_degree0_through7": list(map(rational, tv)),
                    "TV_quotient_recurrence_residual": list(map(rational, s.add(tv, s.scale(alternative, -1)))),
                    "precision": "g0..g6 determine TV through degree 7 because U^-1-1 has constant zero; no g7 or v7 is claimed",
                    "marked_context_definition": "t(G,v)=f(G)*vertex_orbit_size; c counts singleton vertex orbits only when f=1"}


def algebra_checks(rows, sampling_rows=None):
    h, direct = direct_coefficients(rows)
    other, independent = independent_coefficients(rows)
    exact_equal(h, other, "Direct versus independent coefficient route")
    for row in independent["finite_polynomial_stabilization"]:
        exact_equal(row["coefficients"], list(map(rational, h[:row["R"]])),
                    f"Finite-polynomial stabilization at R={row['R']}")
    U, log_coefficients, logarithms = logarithm_checks(h)
    inverse_numerator, inverse = inverse_checks(log_coefficients)
    claims = {f"a{row['n']}": str(row["a"]) for row in rows}
    claims.update({f"r{row['n']}": str(row["r"]) for row in rows})
    claims.update({f"h{k}": rational(value) for k, value in enumerate(h)})
    claims.update({f"q{k}": value for k, value in enumerate(direct["Q"])})
    claims.update({f"u{k}": rational(value) for k, value in enumerate(U)})
    claims.update({f"log_a_b{k}": rational(value) for k, value in enumerate(log_coefficients) if k})
    claims["inverse_second_shift_numerator"] = rational(inverse_numerator)
    claims["tv_leading_coefficient_from_h1"] = rational(-h[1])
    diagnostics = {"direct_recursive_Q": direct, "independent_lagrange_transfer": independent,
                   "formal_logarithm": logarithms, "formal_inverse": inverse}
    if sampling_rows is not None:
        sampling_claims, sampling_details = sampling_algebra_checks(sampling_rows, h)
        claims.update(sampling_claims)
        diagnostics["four_realizer_and_TV"] = sampling_details
    return claims, diagnostics


def enumeration_checks(rows, through=6, methods="both", sampling_rows=None):
    require(type(through) is int and 0 <= through <= 9, "Enumeration limit must be between 0 and 9")
    require(methods in ("both", "degree", "refined"), "Unknown enumeration method")
    from enumeration import enumerate_degree, enumerate_refined
    selected = {"degree": enumerate_degree, "refined": enumerate_refined}
    if methods != "both":
        selected = {methods: selected[methods]}
    result = {name: [] for name in selected}
    for row in rows[:through]:
        for name, enumerate_graphs in selected.items():
            include_sampling = sampling_rows is not None and row["n"] <= len(sampling_rows)
            actual = enumerate_graphs(row["n"], sampling=include_sampling)
            if include_sampling:
                sampling_row = sampling_rows[row["n"]-1]
                for key in ("b", "c"):
                    exact_equal(actual[key], sampling_row[key],
                                f"{name} sampling enumeration n={row['n']} {key}")
            exact_equal(actual["permutations"], factorial(row["n"]),
                        f"{name} exhaustive visitation n={row['n']}")
            for key in ("n", "a", "r"):
                exact_equal(actual[key], row[key], f"{name} enumeration n={row['n']} {key}")
            result[name].append(actual)
    return {"through_n": through, "methods": result,
            "fixed_input_status": "a1..a9 and r1..r9 have two original exhaustive source runs",
            "this_run_status": f"This invocation replays only n=1..{through}" if through else "Algebra only; no enumeration replay in this invocation"}


def run(claims, inputs, through=6, methods="both"):
    rows = validate_inputs(inputs)
    sampling_rows = validate_sampling_inputs(inputs)
    actual, algebra = algebra_checks(rows, sampling_rows)
    exact_equal(set(actual), set(claims), "Claim key set")
    for key in sorted(actual):
        exact_equal(actual[key], claims[key], f"Claim {key}")
    enumeration = enumeration_checks(rows, through, methods, sampling_rows)
    return {"schema": "report153-exact-companion-v2", "status": "passed",
            "arithmetic": "Exact integers and fractions.Fraction; standard library only",
            "scope": "Finite enumeration and formal rational identities; not an analytic theorem or novelty certificate",
            "coefficient_order": ORDER, "claims": actual,
            "fixed_inputs": rows, "sampling_inputs": sampling_rows, "algebra_checks": algebra, "enumeration_checks": enumeration}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--claims", type=Path, default=ROOT / "claims.json")
    parser.add_argument("--inputs", type=Path, default=ROOT / "inputs.json")
    parser.add_argument("--enumerate-through", type=int, choices=range(10), default=6,
                        help="Replay n=1..N, default 6; 0 means algebra only; 9 is exhaustive full replay")
    parser.add_argument("--enumerator", choices=("both", "degree", "refined"), default="both")
    parser.add_argument("--output", type=Path, help="Unused .json path strictly inside companion/results/")
    args = parser.parse_args(argv)
    try:
        data = run(load_claims(args.claims), load_json(args.inputs), args.enumerate_through, args.enumerator)
        if args.output:
            write_new_json(args.output, data)
        print(encoded_json(data), end="")
        return 0
    except (VerificationError, ValueError, OSError, ZeroDivisionError) as exc:
        print(f"Verification failed: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
