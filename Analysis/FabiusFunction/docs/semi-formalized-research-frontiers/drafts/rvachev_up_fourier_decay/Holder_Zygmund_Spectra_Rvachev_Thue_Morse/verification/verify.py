#!/usr/bin/env python3
"""Exact finite algebra checks for trigonometric Markov transfers.

Run: python3 verify.py --output results.json

Only the Python standard library is used.  All scalar calculations use
fractions.Fraction or integers; no numerical eigensolver is used.  These
finite checks complement, and do not replace, the proofs in the article.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction as Q
from pathlib import Path


CHECK_COUNTS: dict[str, int] = {}


def check(condition: bool, group: str, description: str) -> None:
    """Use an explicit exception so checks remain active with python -O."""
    if not condition:
        raise AssertionError(f"{group}: {description}")
    CHECK_COUNTS[group] = CHECK_COUNTS.get(group, 0) + 1


def zero_matrix(n: int) -> list[list[Q]]:
    return [[Q(0) for _ in range(n)] for _ in range(n)]


def identity(n: int) -> list[list[Q]]:
    return [[Q(i == j) for j in range(n)] for i in range(n)]


def matrix_add(a: list[list[Q]], b: list[list[Q]]) -> list[list[Q]]:
    return [[x + y for x, y in zip(ar, br)] for ar, br in zip(a, b)]


def matrix_scale(c: Q, a: list[list[Q]]) -> list[list[Q]]:
    return [[c * x for x in row] for row in a]


def matrix_mul(a: list[list[Q]], b: list[list[Q]]) -> list[list[Q]]:
    bt = list(zip(*b))
    return [[sum((x * y for x, y in zip(row, col)), Q(0))
             for col in bt] for row in a]


def matrix_vector(a: list[list[Q]], v: list[Q]) -> list[Q]:
    return [sum((x * y for x, y in zip(row, v)), Q(0)) for row in a]


def rank(a: list[list[Q]]) -> int:
    """Exact Gaussian elimination over Q."""
    work = [row[:] for row in a]
    if not work:
        return 0
    r = 0
    for c in range(len(work[0])):
        pivot = next((i for i in range(r, len(work)) if work[i][c]), None)
        if pivot is None:
            continue
        work[r], work[pivot] = work[pivot], work[r]
        denominator = work[r][c]
        work[r] = [x / denominator for x in work[r]]
        for i in range(r + 1, len(work)):
            multiplier = work[i][c]
            if multiplier:
                work[i] = [x - multiplier * y
                           for x, y in zip(work[i], work[r])]
        r += 1
        if r == len(work):
            break
    return r


def poly_trim(p: list[Q]) -> list[Q]:
    """Polynomial coefficients are always in ascending degree order."""
    p = p[:]
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return p or [Q(0)]


def poly_mul(p: list[Q], q: list[Q]) -> list[Q]:
    out = [Q(0)] * (len(p) + len(q) - 1)
    for i, x in enumerate(p):
        for j, y in enumerate(q):
            out[i + j] += x * y
    return poly_trim(out)


def poly_product(factors: list[list[Q]]) -> list[Q]:
    result = [Q(1)]
    for factor in factors:
        result = poly_mul(result, factor)
    return result


def poly_divmod(p: list[Q], q: list[Q]) -> tuple[list[Q], list[Q]]:
    p, q = poly_trim(p), poly_trim(q)
    if q == [Q(0)]:
        raise ZeroDivisionError("zero polynomial")
    quotient = [Q(0)] * max(1, len(p) - len(q) + 1)
    while p != [Q(0)] and len(p) >= len(q):
        shift = len(p) - len(q)
        coefficient = p[-1] / q[-1]
        quotient[shift] += coefficient
        for j, value in enumerate(q):
            p[j + shift] -= coefficient * value
        p = poly_trim(p)
    return poly_trim(quotient), p


def poly_gcd(p: list[Q], q: list[Q]) -> list[Q]:
    p, q = poly_trim(p), poly_trim(q)
    while q != [Q(0)]:
        _, remainder = poly_divmod(p, q)
        p, q = q, remainder
    return [x / p[-1] for x in p] if p != [Q(0)] else p


def derivative(p: list[Q]) -> list[Q]:
    return poly_trim([i * p[i] for i in range(1, len(p))])


def matrix_polynomial(p: list[Q], a: list[list[Q]]) -> list[list[Q]]:
    unit = identity(len(a))
    out = zero_matrix(len(a))
    for coefficient in reversed(p):
        out = matrix_add(matrix_mul(out, a), matrix_scale(coefficient, unit))
    return out


def charpoly(a: list[list[Q]]) -> list[Q]:
    """Faddeev--LeVerrier algorithm, performed exactly over Q."""
    n = len(a)
    unit = identity(n)
    b = unit
    descending = [Q(1)]
    for k in range(1, n + 1):
        ab = matrix_mul(a, b)
        coefficient = -sum((ab[i][i] for i in range(n)), Q(0)) / k
        descending.append(coefficient)
        b = matrix_add(ab, matrix_scale(coefficient, unit))
    return list(reversed(descending))


def clean(f: dict[int, Q]) -> dict[int, Q]:
    return {k: Q(v) for k, v in f.items() if v}


def fourier_add(f: dict[int, Q], g: dict[int, Q]) -> dict[int, Q]:
    result = dict(f)
    for k, value in g.items():
        result[k] = result.get(k, Q(0)) + value
    return clean(result)


def fourier_scale(c: Q, f: dict[int, Q]) -> dict[int, Q]:
    return clean({k: c * value for k, value in f.items()})


def fourier_mul(f: dict[int, Q], g: dict[int, Q]) -> dict[int, Q]:
    result: dict[int, Q] = {}
    for k, x in f.items():
        for ell, y in g.items():
            result[k + ell] = result.get(k + ell, Q(0)) + x * y
    return clean(result)


def transfer(b: int, weight: dict[int, Q], f: dict[int, Q]) -> dict[int, Q]:
    """T e_ell = sum_{k: b*k-ell in supp(weight)} a_hat(b*k-ell) e_k."""
    product = fourier_mul(weight, f)
    return clean({index // b: value for index, value in product.items()
                  if index % b == 0})


def compose_dilation(b: int, f: dict[int, Q]) -> dict[int, Q]:
    """U_b f(x) = f(b*x), hence U_b e_k = e_(b*k)."""
    return {b * k: value for k, value in f.items()}


def core_matrix(b: int, weight: dict[int, Q]) -> tuple[list[int], list[list[Q]]]:
    d = max(abs(k) for k, value in weight.items() if value)
    kmax = d // (b - 1)
    indices = list(range(-kmax, kmax + 1))
    a = [[weight.get(b * k - ell, Q(0)) for ell in indices] for k in indices]
    return indices, a


def encode_poly(p: list[Q]) -> list[str]:
    return [str(coefficient) for coefficient in p]


def encode_fourier(f: dict[int, Q]) -> dict[str, str]:
    return {str(k): str(f[k]) for k in sorted(f)}


def check_core(d: int) -> dict:
    group = f"core_b2_d{d}"
    weight = {0: Q(1), -d: Q(-1, 2), d: Q(-1, 2)}
    check(transfer(2, weight, {0: Q(1)}) == {0: Q(1)}, group, "T(1)=1")
    nonnegative_factorization = fourier_scale(
        Q(1, 2), fourier_mul({0: Q(1), d: Q(-1)}, {0: Q(1), -d: Q(-1)})
    )
    check(weight == nonnegative_factorization, group,
          "a = (1-e_d)(1-e_-d)/2")
    indices, a = core_matrix(2, weight)
    unit = identity(len(a))
    p = charpoly(a)
    one = [Q(-1), Q(1)]
    minus_half = [Q(1, 2), Q(1)]
    irreducible_factors = [one, minus_half]
    if d == 3:
        irreducible_factors.extend([
            [Q(1, 2), Q(-1, 2), Q(1)],
            [Q(1, 2), Q(1, 2), Q(1)],
        ])
    expected = poly_product(irreducible_factors + [minus_half])
    check(p == expected, group, "characteristic polynomial factorization")
    check(matrix_polynomial(p, a) == zero_matrix(len(a)), group,
          "Cayley--Hamilton identity")
    gcd = poly_gcd(p, derivative(p))
    check(gcd == minus_half, group, "gcd(characteristic polynomial, derivative)")
    minimal = poly_product(irreducible_factors)
    check(matrix_polynomial(minimal, a) == zero_matrix(len(a)), group,
          "proposed minimal polynomial annihilates A")
    check(poly_gcd(minimal, derivative(minimal)) == [Q(1)], group,
          "minimal polynomial is squarefree")
    for i in range(len(irreducible_factors)):
        omitted = poly_product(irreducible_factors[:i] + irreducible_factors[i + 1:])
        check(matrix_polynomial(omitted, a) != zero_matrix(len(a)), group,
              f"irreducible factor {i + 1} is necessary")
    ranks = {}
    for eigenvalue, multiplicity in [(Q(1), 1), (Q(-1, 2), 2)]:
        r = rank(matrix_add(a, matrix_scale(-eigenvalue, unit)))
        check(len(a) - r == multiplicity, group,
              f"dimension of eigenspace {eigenvalue}")
        ranks[str(eigenvalue)] = {
            "rank_A_minus_lambda_I": r,
            "eigenspace_dimension": len(a) - r,
            "algebraic_multiplicity": multiplicity,
        }
    if d == 3:
        # The quadratics have negative discriminant and are irreducible over Q.
        for factor in irreducible_factors[2:]:
            discriminant = factor[1] ** 2 - 4 * factor[2] * factor[0]
            check(discriminant == Q(-7, 4), group,
                  "quadratic discriminant is -7/4")
    # Verify the core matrix against the direct Fourier implementation.
    for ell in indices:
        direct = transfer(2, weight, {ell: Q(1)})
        from_matrix = clean({k: a[row][indices.index(ell)]
                             for row, k in enumerate(indices)})
        check(direct == from_matrix, group, f"core column ell={ell}")
    result = {
        "b": 2,
        "weight_degree": d,
        "weight_fourier_coefficients": encode_fourier(weight),
        "core_indices": indices,
        "core_matrix": [[str(x) for x in row] for row in a],
        "polynomial_coefficient_order": "ascending",
        "characteristic_polynomial": encode_poly(p),
        "characteristic_factorization": (
            "(z-1)*(z+1/2)^2" if d == 1 else
            "(z-1)*(2*z+1)^2*(2*z^2-z+1)*(2*z^2+z+1)/16"
        ),
        "gcd_charpoly_derivative": encode_poly(gcd),
        "minimal_polynomial": encode_poly(minimal),
        "minimal_polynomial_squarefree": True,
        "diagonalizable_over_C": True,
        "rational_eigenvalue_ranks": ranks,
    }
    if d == 1:
        # A is real rational, so real and imaginary coefficient parts may
        # be checked separately without introducing approximate complex data.
        modes = [
            ("1", Q(1), [Q(0), Q(1), Q(0)], [Q(0)] * 3),
            ("sin(2*pi*x)", Q(-1, 2), [Q(0)] * 3,
             [Q(1, 2), Q(0), Q(-1, 2)]),
            ("cos(2*pi*x)+1/3", Q(-1, 2),
             [Q(1, 2), Q(1, 3), Q(1, 2)], [Q(0)] * 3),
        ]
        mode_results = []
        for name, eigenvalue, real, imag in modes:
            check(matrix_vector(a, real) == [eigenvalue * v for v in real],
                  group, f"real coefficients of mode {name}")
            check(matrix_vector(a, imag) == [eigenvalue * v for v in imag],
                  group, f"imaginary coefficients of mode {name}")
            mode_results.append({
                "mode": name,
                "eigenvalue": str(eigenvalue),
                "coefficients_in_core_order": [
                    {"real": str(x), "imaginary": str(y)}
                    for x, y in zip(real, imag)
                ],
            })
        result["explicit_eigenmodes"] = mode_results
        basis = [[Q(0), Q(-1), Q(1, 2)],
                 [Q(1), Q(0), Q(1, 3)],
                 [Q(0), Q(1), Q(1, 2)]]
        check(rank(basis) == 3, group, "explicit eigenmodes form a complex basis")
    return result


def degree_step(b: int, d: int, degree: int) -> int:
    return (degree + d) // b


def check_degree_identities() -> dict:
    group = "degree_identities"
    cases = 0
    for b in range(2, 8):
        for d in range(16):
            core = d // (b - 1)
            check(degree_step(b, d, core) == core, group,
                  f"core fixed degree b={b}, d={d}")
            for m in range(core, core + 9):
                for n in range(9):
                    geometric = sum(b ** j for j in range(n))
                    threshold = b ** n * (m + 1) - d * geometric - 1
                    rho = Q(d, b - 1)
                    transformed = Q(threshold + 1) - rho
                    check(transformed == b ** n * (Q(m + 1) - rho), group,
                          "affine coordinate transforms by b^n")
                    recursive = m
                    for _ in range(n):
                        recursive = b * (recursive + 1) - d - 1
                    check(recursive == threshold, group,
                          "closed formula equals recursive threshold")
                    check(threshold >= m, group,
                          "threshold is at least the invariant core degree")
                    value, next_value = threshold, threshold + 1
                    for _ in range(n):
                        value = degree_step(b, d, value)
                        next_value = degree_step(b, d, next_value)
                    check(value == m, group,
                          "iterated formal degree at threshold equals M")
                    check(next_value == m + 1, group,
                          "threshold is sharp for formal degree recurrence")
                    check((threshold + d * geometric) // b ** n == m, group,
                          "closed formula for iterated degree bound")
                    cases += 1
    return {
        "b_range_inclusive": [2, 7],
        "d_range_inclusive": [0, 15],
        "M_values": "floor(d/(b-1)) through floor(d/(b-1))+8",
        "n_range_inclusive": [0, 8],
        "parameter_cases": cases,
        "core_fixed_degree_cases": 96,
        "threshold_formula": "N_n(M)=b^n*(M+1)-d*sum(b^j,j=0..n-1)-1",
        "affine_identity": "N_n(M)+1-d/(b-1)=b^n*(M+1-d/(b-1))",
        "formal_recurrence": "D(L)=floor((L+d)/b)",
        "scope": (
            "Finite exact checks of a formal degree inequality. Positive d "
            "divisible by b cannot be the actual degree of a normalized weight; "
            "those parameter values test the algebraic formula only. Sharpness "
            "here refers to the formal recurrence, not every actual weight."
        ),
    }


def check_defects_and_series() -> dict:
    group = "defects_and_truncated_series"
    weight = {0: Q(1), -1: Q(-1, 2), 1: Q(-1, 2)}
    p = lambda f: transfer(2, weight, f)
    u = lambda f: compose_dilation(2, f)
    for j in range(1, 33):
        defect = {2 * j + 1: Q(1), 2 * j: Q(1, 2), 2 * j + 2: Q(1, 2)}
        check(p(defect) == {}, group, f"kernel defect j={j}")
    for frequency in range(-64, 65):
        mode = {frequency: Q(1)}
        check(p(u(mode)) == mode, group, f"P U e_{frequency}=e_{frequency}")
    eigenvalue = Q(-1, 2)
    h = {0: Q(1, 3), 1: Q(1)}
    check(p(h) == fourier_scale(eigenvalue, h), group, "P h=lambda h")
    max_n = 16
    dilations = [h]
    partial_sums = [h]
    for k in range(1, max_n + 1):
        dilations.append(u(dilations[-1]))
        partial_sums.append(fourier_add(
            partial_sums[-1], fourier_scale(eigenvalue ** k, dilations[k])
        ))
    iterated_cases = 0
    for capital_n, f in enumerate(partial_sums):
        actual = fourier_add(p(f), fourier_scale(-eigenvalue, f))
        expected = fourier_add(
            fourier_scale(eigenvalue, h),
            fourier_scale(-eigenvalue ** (capital_n + 1), dilations[capital_n]),
        )
        check(actual == expected, group, f"(P-lambda)F_N remainder N={capital_n}")
        iterated = f
        for n in range(capital_n + 1):
            expected = fourier_scale(eigenvalue ** n, fourier_add(
                fourier_scale(Q(n), h), partial_sums[capital_n - n]
            ))
            check(iterated == expected, group,
                  f"P^n F_N=lambda^n*(n*h+F_(N-n)), N={capital_n}, n={n}")
            iterated_cases += 1
            iterated = p(iterated)
    return {
        "kernel_defect": "e_(2*j+1)+(e_(2*j)+e_(2*j+2))/2",
        "kernel_defect_j_range_inclusive": [1, 32],
        "P_U_character_frequencies_inclusive": [-64, 64],
        "lambda": str(eigenvalue),
        "h_fourier_coefficients": encode_fourier(h),
        "F_N_definition": "sum(lambda^k*U^k*h,k=0..N)",
        "truncation_range_inclusive": [0, max_n],
        "remainder_identity": "(P-lambda)F_N=lambda*h-lambda^(N+1)*U^N*h",
        "iterated_identity": "P^n F_N=lambda^n*(n*h+F_(N-n)), 0<=n<=N",
        "iterated_identity_cases": iterated_cases,
        "largest_character_frequency": 2 ** max_n,
        "scope": "Finite Fourier polynomials only; no infinite series convergence is tested.",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("results.json"))
    args = parser.parse_args()
    CHECK_COUNTS.clear()
    results = {
        "verification_status": "passed",
        "arithmetic": "exact rational and integer arithmetic; Python standard library",
        "polynomial_coefficient_convention": "ascending degree",
        "fourier_convention": "e_k(x)=exp(2*pi*i*k*x)",
        "transfer_convention": "T e_ell=sum_k a_hat(b*k-ell)*e_k",
        "core_examples": [check_core(1), check_core(3)],
        "degree_identities": check_degree_identities(),
        "defects_and_series": check_defects_and_series(),
        "limits": [
            "Finite algebraic verification does not prove the article's general theorems.",
            "No claim of research priority or novelty is established computationally.",
            "Infinite dimensional spectral conclusions require the analytic proofs.",
        ],
    }
    results["check_counts"] = dict(sorted(CHECK_COUNTS.items()))
    results["total_checks"] = sum(CHECK_COUNTS.values())
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(results, indent=2, sort_keys=True) + "\n",
                           encoding="utf-8")
    print(f"PASS: {results['total_checks']} exact checks; results written to {args.output}")


if __name__ == "__main__":
    main()
