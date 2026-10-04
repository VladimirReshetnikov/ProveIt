#!/usr/bin/env python3
"""Fresh finite-difference and coefficient evidence; no source code is imported.

Only explicit integer arrays and polynomial coefficients are manipulated.
No counter semantics, physical dynamics, acceptance-table interpreter, upstream
code, or proof assistant is executed. The all-horizon sign proof is in PROOF.md.
"""
from math import comb, factorial
from pathlib import Path
import hashlib
import json


def differences(values):
    row = list(values)
    first = []
    while row:
        first.append(row[0])
        row = [right - left for left, right in zip(row, row[1:])]
    return first


def trim(coefficients):
    result = list(coefficients)
    while result and result[-1] == 0:
        result.pop()
    return result


def add_scaled(left, right, scale=1):
    out = list(left) + [0] * max(0, len(right) - len(left))
    for i, value in enumerate(right):
        out[i] += scale * value
    return trim(out)


def multiply(left, right):
    if not left or not right:
        return []
    out = [0] * (len(left) + len(right) - 1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            out[i+j] += a*b
    return trim(out)


def evaluate(coefficients, x):
    value = 0
    for coefficient in reversed(coefficients):
        value = value*x + coefficient
    return value


def compose_affine(coefficients, offset, slope):
    result = []
    for coefficient in reversed(coefficients):
        result = add_scaled(multiply(result, [offset, slope]), [coefficient])
    return result


def cleared_newton(values):
    c = factorial(len(values)-1)
    result, basis = [], [1]
    for order, value in enumerate(differences(values)):
        assert c % factorial(order) == 0
        result = add_scaled(result, basis, value*(c//factorial(order)))
        basis = multiply(basis, [-(order+1), 1])
    return result


def formula(K):
    N = K*K
    if K == 1:
        return 0, 1
    if K % 2 == 0:
        return N-1, -sum(comb(N-2, h*K-1) for h in range(1, K))
    alternating = sum((-1)**(h+1)*comb(N-3, h*K-1)
                      for h in range(1, K))
    return N-2, (N-1)*alternating


# Multivariate dictionaries have fixed exponent order (j,A,B,r,s).
ZERO = (0, 0, 0, 0, 0)


def p_constant(value):
    return {ZERO: value} if value else {}


def p_variable(index):
    exponent = tuple(1 if i == index else 0 for i in range(5))
    return {exponent: 1}


def p_add(left, right, scale=1):
    out = dict(left)
    for exponent, coefficient in right.items():
        out[exponent] = out.get(exponent, 0) + scale*coefficient
        if out[exponent] == 0:
            del out[exponent]
    return out


def p_multiply(left, right):
    out = {}
    for e, a in left.items():
        for f, b in right.items():
            g = tuple(e[i]+f[i] for i in range(5))
            out[g] = out.get(g, 0) + a*b
    return {e: a for e, a in out.items() if a}


def embed(coefficients):
    return {(i, 0, 0, 0, 0): c for i, c in enumerate(coefficients) if c}


def product_roots(roots):
    result = [1]
    for root in roots:
        result = multiply(result, [-root, 1])
    return result


def complete_polynomial(K, accepted, U, V):
    N = K*K
    c = factorial(N-1)
    U, V = embed(U), embed(V)
    A, B, r, s = (p_variable(i) for i in (1, 2, 3, 4))
    first_A = p_add(p_add({}, A, c), U, -1)
    first_B = p_add(p_add({}, B, c), V, -1)
    residuals = [
        embed(product_roots(range(1, N+1))),
        p_multiply(first_A, p_add(U, p_constant(-c*K))),
        p_add(p_add(first_A, r, -c), p_constant(c)),
        p_multiply(first_B, p_add(V, p_constant(-c*K))),
        p_add(p_add(first_B, s, -c), p_constant(c)),
        embed(product_roots(sorted(accepted))),
    ]
    total = {}
    for residual in residuals:
        total = p_add(total, p_multiply(residual, residual))
    return residuals, total


def main():
    report = {"scope": "exact finite arrays and polynomial coefficients only",
              "finite_differences": [], "full_interpolants": [],
              "six_square_expansions": []}
    interpolants = {}
    for K in range(1, 41):
        N, c = K*K, factorial(K*K-1)
        u = [(i-1)//K+1 for i in range(1, N+1)]
        v = [(i-1)%K+1 for i in range(1, N+1)]
        du, dv = differences(u), differences(v)
        degree, a = formula(K)
        actual_u = max(i for i, value in enumerate(du) if value)
        actual_v = max(i for i, value in enumerate(dv) if value)
        assert actual_u == actual_v == degree
        assert c*du[degree]//factorial(degree) == a
        if K >= 2:
            assert c*dv[degree]//factorial(degree) == -K*a
            expected_sign = -1 if K % 2 == 0 else (-1)**((K+1)//2)
            assert (1 if a > 0 else -1) == expected_sign
            assert 4*degree > 2*N
        if K >= 3 and K % 2:
            assert du[-1] == dv[-1] == 0
            assert du[-2] == sum((-1)**(h+1)*comb(N-3, h*K-1)
                                 for h in range(1, K))
        report["finite_differences"].append({
            "K": K, "N": N, "interpolant_degree": degree,
            "cleared_U_leading_coefficient": str(a),
            "native_SOS_degree": 2 if K == 1 else 4*degree,
        })
        if K <= 9:
            U, V = cleared_newton(u), cleared_newton(v)
            assert len(U)-1 == len(V)-1 == degree
            assert U[-1] == a
            for i in range(1, N+1):
                assert evaluate(U, i) == c*u[i-1]
                assert evaluate(V, i) == c*v[i-1]
            reflected = compose_affine(U, N+1, -1)
            assert reflected == add_scaled([c*(K+1)], U, -1)
            if K >= 2:
                assert V == add_scaled([c*K, c], U, -K)
                assert V[-1] == -K*a
            interpolants[K] = (U, V)
            report["full_interpolants"].append({
                "K": K, "nodes_checked": N,
                "reflection_identity": True,
                "affine_U_V_identity": K >= 2,
            })

    for K in range(1, 8):
        N = K*K
        degree, a = formula(K)
        U, V = interpolants[K]
        if K <= 2:
            tables = [{i+1 for i in range(N) if mask & (1 << i)}
                      for mask in range(1 << N)]
        else:
            tables = [set(), set(range(1, N+1)),
                      set(range(1, N+1, 2)), set(range(1, K+1))]
        for accepted in tables:
            residuals, total = complete_polynomial(K, accepted, U, V)
            expected = 2 if K == 1 else 4*degree
            actual = max(map(sum, total))
            assert len(residuals) == 6 and actual == expected
            top = {exponent: value for exponent, value in total.items()
                   if sum(exponent) == expected}
            if K >= 2:
                assert top == {(4*degree, 0, 0, 0, 0): (1+K**4)*a**4}
                assert len(total) <= 16*degree+11
            else:
                assert len(total) == 9
            report["six_square_expansions"].append({
                "K": K, "accepted": sorted(accepted),
                "joint_total_degree": actual,
                "nonzero_monomials": len(total),
                "top_monomial_count": len(top),
                "top_coefficient_matches_formula": K >= 2,
            })

    script = Path(__file__).resolve()
    report["checker_sha256"] = hashlib.sha256(script.read_bytes()).hexdigest()
    report["summary"] = {
        "K_values_with_full_difference_tables": 40,
        "K_values_with_reconstructed_interpolants": 9,
        "interpolation_nodes_checked": sum(range(1, 10)[i]**2 for i in range(9)),
        "complete_SOS_expansions_checked": len(report["six_square_expansions"]),
        "status": "all assertions passed",
    }
    target = script.parent / "evidence" / "exact_degree_results.json"
    target.write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps(report["summary"], indent=2))


if __name__ == "__main__":
    main()
