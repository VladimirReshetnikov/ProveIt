#!/usr/bin/env python3
"""Finite high-precision checks for the prime-power resonance theorem.

This is a numerical verification artifact, not a proof of the asymptotic
theorems or an interval-arithmetic certificate.  It uses the exact finite
prime-side formula for K, evaluated with mpmath at 90 decimal digits.
No table of zeta zeros and no floating-point eigensolver are used.

Run from any directory:
    python3 verify_resonance.py
The JSON record is written to ../results/verification.json.
"""

from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path

import mpmath as mp


mp.mp.dps = 90
N = 8
D = 1 - mp.euler - mp.log(2 * mp.pi)
K0 = 2 + mp.euler - mp.log(4 * mp.pi)
H_VALUES = ("1e-3", "1e-5", "1e-8", "1e-12")
ROUNDING_ALLOWANCE = mp.mpf("1e-78")


def decimal(value: mp.mpf, digits: int = 45) -> str:
    return mp.nstr(value, digits)


def prime_power(n: int) -> tuple[int, int] | None:
    """Return (p,k) for n=p**k, or None, using integer arithmetic."""
    if n < 2:
        return None
    p = 2
    while p * p <= n and n % p:
        p += 1
    if p * p > n:
        return n, 1
    m, k = n, 0
    while m % p == 0:
        m //= p
        k += 1
    return (p, k) if m == 1 else None


def primes_through(n: int) -> list[int]:
    return [p for p in range(2, n + 1) if prime_power(p) == (p, 1)]


def trivial_zero_tail(t: mp.mpf) -> mp.mpf:
    """Closed form for sum_{k>=1} exp(-2*k*t)/(2*k*(2*k+1))."""
    if t == 0:
        return 1 - mp.log(2)
    # This algebraic form avoids subtraction of separately divergent logs.
    em1 = mp.expm1(t)
    return (1 + em1 * mp.log(-mp.expm1(-t)) / 2
            - (em1 + 2) * mp.log1p(mp.exp(-t)) / 2)


def kernel(t: mp.mpf) -> mp.mpf:
    """The even exact prime-side kernel; only n <= exp(abs(t)) occur."""
    t = abs(mp.mpf(t))
    if t == 0:
        return K0
    x = mp.exp(t)
    upper = int(mp.floor(x))
    if upper > 100000:
        raise ValueError("This verification script is intended for short lags.")
    terms = []
    for n in range(2, upper + 1):
        pk = prime_power(n)
        if pk is not None:
            p, _ = pk
            terms.append(mp.log(p) * (-mp.expm1(mp.log(n) - t)) / n)
    prime_sum = mp.fsum(terms)
    return (mp.exp(t / 2) * (prime_sum - t + 1 + mp.euler)
            - mp.exp(-t / 2) * mp.log(2 * mp.pi)
            + mp.exp(-t / 2) * trivial_zero_tail(t))


def centered_second_difference(a: mp.mpf, h: mp.mpf) -> mp.mpf:
    return 2 * kernel(a) - kernel(a + h) - kernel(a - h)


def variance(h: mp.mpf) -> mp.mpf:
    return 2 * (K0 - kernel(h))


def increment_covariance(a: mp.mpf, h: mp.mpf,
                         u: mp.mpf, v: mp.mpf) -> mp.mpf:
    return (kernel(a + h * (u - v)) - kernel(a + h * u)
            - kernel(a - h * v) + kernel(a))


def brownian_kernel(u: mp.mpf, v: mp.mpf) -> mp.mpf:
    return (abs(u) + abs(v) - abs(u - v)) / 2


def flog(x: mp.mpf) -> mp.mpf:
    return abs(x) * mp.log(abs(x)) if x else mp.mpf(0)


def trace(M: mp.matrix) -> mp.mpf:
    return mp.fsum(M[i, i] for i in range(M.rows))


def max_abs(M: mp.matrix) -> mp.mpf:
    return max(abs(M[i, j]) for i in range(M.rows) for j in range(M.cols))


def arithmetic_matrix(n: int) -> mp.matrix:
    A = mp.matrix(n)
    for i in range(1, n + 1):
        for j in range(i + 1, n + 1):
            if j % i == 0:
                pk = prime_power(j // i)
                if pk is not None:
                    p, _ = pk
                    A[i - 1, j - 1] = A[j - 1, i - 1] = (
                        mp.log(p) / mp.sqrt(mp.mpf(j // i)))
    return A


def correlation_matrix(n: int, h: mp.mpf) -> mp.matrix:
    R = mp.eye(n)
    V = variance(h)
    for i in range(1, n + 1):
        for j in range(i + 1, n + 1):
            lag = mp.log(mp.mpf(j) / i)
            R[i - 1, j - 1] = R[j - 1, i - 1] = (
                centered_second_difference(lag, h) / V)
    return R


def formal_trace_checks(n: int) -> dict:
    """Exact rational coefficients of (log p)^2 and (log p)^3."""
    edge: dict[tuple[int, int], tuple[int, int]] = {}
    matrix_s2: dict[int, Fraction] = {}
    matrix_s3: dict[int, Fraction] = {}
    for i in range(1, n + 1):
        for j in range(i + 1, n + 1):
            pk = prime_power(j // i) if j % i == 0 else None
            if pk is not None:
                p, _ = pk
                edge[i, j] = (p, j // i)
                matrix_s2[p] = matrix_s2.get(p, Fraction()) + Fraction(i, j)
    triangle_count = 0
    for i in range(1, n + 1):
        for j in range(i + 1, n + 1):
            for k in range(j + 1, n + 1):
                if all(e in edge for e in ((i, j), (j, k), (i, k))):
                    p1, r1 = edge[i, j]
                    p2, r2 = edge[j, k]
                    p3, r3 = edge[i, k]
                    assert p1 == p2 == p3
                    assert r1 * r2 == r3
                    assert r1 * r2 * r3 == r3 * r3
                    matrix_s3[p1] = matrix_s3.get(p1, Fraction()) + Fraction(2, r3)
                    triangle_count += 1
    formula_s2: dict[int, Fraction] = {}
    formula_s3: dict[int, Fraction] = {}
    for p in primes_through(n):
        power, exponent = p, 1
        while power <= n:
            formula_s2[p] = formula_s2.get(p, Fraction()) + Fraction(n // power, power)
            if exponent >= 2:
                formula_s3[p] = (formula_s3.get(p, Fraction())
                                 + Fraction(2 * (n // power) * (exponent - 1), power))
            power *= p
            exponent += 1
    assert matrix_s2 == formula_s2
    assert matrix_s3 == formula_s3
    return {
        "status": "passed: exact rational coefficient identities",
        "edge_count": len(edge), "triangle_count": triangle_count,
        "S2_coefficients_of_log_p_squared": {str(p): str(c) for p, c in formula_s2.items()},
        "S3_coefficients_of_log_p_cubed": {str(p): str(c) for p, c in formula_s3.items()},
    }


def check_tail_formula() -> list[dict]:
    rows = []
    M = 3000
    for t in (mp.mpf("0.1"), mp.mpf("0.3"), mp.log(2), mp.log(8)):
        finite = mp.fsum(mp.exp(-2 * k * t) / (2 * k * (2 * k + 1))
                         for k in range(1, M + 1))
        tail_bound = (mp.exp(-2 * (M + 1) * t)
                      / (2 * (M + 1) * (2 * (M + 1) + 1)
                         * (-mp.expm1(-2 * t))))
        discrepancy = abs(trivial_zero_tail(t) - finite)
        assert discrepancy <= tail_bound + ROUNDING_ALLOWANCE
        rows.append({"t": decimal(t), "terms": M,
                     "absolute_discrepancy": decimal(discrepancy),
                     "geometric_tail_bound": decimal(tail_bound)})
    return rows


def exact_gauge_checks(n: int) -> list[dict]:
    """Character gauges and exact symbolic trace polynomials through order 8.

    Conjugation by diag(sqrt(1),...,sqrt(n)) changes an upper edge for
    j/i=p**k into log(p)/p**k and the reverse edge into log(p).  Thus
    traces can be computed as polynomials in formal log-prime symbols
    using rational arithmetic alone.
    """
    primes = primes_through(n)
    position = {p: j for j, p in enumerate(primes)}
    unit_monomial = (0,) * len(primes)

    def symbolic_traces(character_values: list[int] | None,
                        modulus: int) -> dict[int, dict[tuple[int, ...], Fraction]]:
        sparse = [[] for _ in range(n)]
        for i in range(1, n + 1):
            for j in range(i + 1, n + 1):
                pk = prime_power(j // i) if j % i == 0 else None
                if pk is None:
                    continue
                p, _ = pk
                if character_values is None:
                    sign = 0 if modulus % p == 0 else 1
                else:
                    sign = character_values[(j // i) % modulus]
                if sign:
                    sparse[i - 1].append((j - 1, position[p], Fraction(sign * i, j)))
                    sparse[j - 1].append((i - 1, position[p], Fraction(sign)))
        current = [[{} for _ in range(n)] for _ in range(n)]
        for i in range(n):
            current[i][i] = {unit_monomial: Fraction(1)}
        traces = {}
        for degree in range(1, 9):
            nxt = [[{} for _ in range(n)] for _ in range(n)]
            for i in range(n):
                for middle in range(n):
                    for monomial, coefficient in current[i][middle].items():
                        for j, which_prime, edge_coefficient in sparse[middle]:
                            new_monomial = list(monomial)
                            new_monomial[which_prime] += 1
                            new_monomial = tuple(new_monomial)
                            destination = nxt[i][j]
                            destination[new_monomial] = (destination.get(new_monomial, Fraction())
                                                         + coefficient * edge_coefficient)
            current = nxt
            diagonal = {}
            for i in range(n):
                for monomial, coefficient in current[i][i].items():
                    diagonal[monomial] = diagonal.get(monomial, Fraction()) + coefficient
            traces[degree] = {m: c for m, c in diagonal.items() if c}
        return traces

    def serial_polynomial(poly: dict[tuple[int, ...], Fraction]) -> dict[str, str]:
        result = {}
        for monomial, coefficient in sorted(poly.items()):
            label = " * ".join(f"log({p})^{k}" for p, k in zip(primes, monomial) if k)
            result[label or "1"] = str(coefficient)
        return result

    rows = []
    characters = (
        ("chi_minus_4", 4, [0, 1, 0, -1]),
        ("chi_8", 8, [0, 1, 0, -1, 0, -1, 0, 1]),
        ("chi_minus_8", 8, [0, 1, 0, 1, 0, -1, 0, -1]),
    )
    for name, q, values in characters:
        ramified = [p for p in primes_through(q) if q % p == 0]
        signs = []
        for i in range(1, n + 1):
            unit = i
            for p in ramified:
                while unit % p == 0:
                    unit //= p
            signs.append(values[unit % q])
        assert all(sign in (-1, 1) for sign in signs)
        checked_edges, nonzero_edges = 0, 0
        for i in range(1, n + 1):
            for j in range(i + 1, n + 1):
                pk = prime_power(j // i) if j % i == 0 else None
                if pk is not None:
                    p, _ = pk
                    deleted_coefficient = 0 if q % p == 0 else 1
                    character_coefficient = values[(j // i) % q]
                    assert character_coefficient == signs[i - 1] * signs[j - 1] * deleted_coefficient
                    nonzero_edges += int(deleted_coefficient != 0)
                checked_edges += 1
        signed_traces = symbolic_traces(values, q)
        deleted_traces = symbolic_traces(None, q)
        assert signed_traces == deleted_traces
        rows.append({
            "name": name, "conductor": q, "character_residue_values": values,
            "ramified_primes": ramified, "gauge_diagonal": signs,
            "checked_off_diagonal_pairs": checked_edges,
            "remaining_undirected_edges": nonzero_edges,
            "exact_entrywise_gauge_error": 0,
            "gauge_identity": "A_chi = D A_ramified_deleted D, D^2 = I",
            "all_orders_trace_identity": "Follows algebraically from the verified similarity; every trace polynomial through degree 8 also checked by an independent rational polynomial multiplication.",
            "trace_polynomial_orders_checked": list(range(1, 9)),
            "exact_trace_polynomials": {str(k): serial_polynomial(poly)
                                        for k, poly in deleted_traces.items()},
            "trace_polynomial_discrepancies": {str(k): {} for k in range(1, 9)},
        })
    assert all(row["exact_trace_polynomials"] == rows[0]["exact_trace_polynomials"]
               for row in rows[1:])
    return rows


def main() -> None:
    A = arithmetic_matrix(N)
    A2, A3 = A ** 2, A ** 3
    S2, S3 = trace(A2) / 2, trace(A3) / 3
    explicit_s2, explicit_s3 = mp.mpf(0), mp.mpf(0)
    for p in primes_through(N):
        power, k = p, 1
        while power <= N:
            explicit_s2 += (N // power) * mp.log(p) ** 2 / power
            if k >= 2:
                explicit_s3 += 2 * (N // power) * (k - 1) * mp.log(p) ** 3 / power
            power *= p
            k += 1
    assert abs(S2 - explicit_s2) < ROUNDING_ALLOWANCE
    assert abs(S3 - explicit_s3) < ROUNDING_ALLOWANCE

    matrix_rows, diagonal_rows, general_rows = [], [], []
    inf_norm_A = max(mp.fsum(abs(A[i, j]) for j in range(N)) for i in range(N))
    pair_values = (("0.3", "0.8"), ("0.8", "0.3"),
                   ("-0.4", "0.8"), ("-0.2", "-0.7"), ("0.9", "0.9"))
    for h_text in H_VALUES:
        h = mp.mpf(h_text)
        L, ell = mp.log(1 / h), mp.log(1 / h) + D
        V = variance(h)
        assert V > 0
        variance_error = V - h * ell
        assert abs(variance_error) < 10 * h ** 2
        diagonal_rows.append({
            "h": h_text, "variance": decimal(V), "ell": decimal(ell),
            "variance_minus_h_ell": decimal(variance_error),
            "variance_remainder_divided_by_h_squared": decimal(variance_error / h ** 2),
        })
        R = correlation_matrix(N, h)
        mp.cholesky(R)  # Independent positive-definiteness check at 90 digits.
        det_R = mp.det(R)
        assert det_R > 0
        loss = -mp.log(det_R)
        approximation_error = max_abs(ell * (mp.eye(N) - R) - A)
        assert approximation_error < 50 * h * (1 + L)
        ideal = mp.eye(N) - A / ell
        ideal_loss = -mp.log(mp.det(ideal))
        assert abs(loss - ideal_loss) < 100 * h / ell
        # A rigorously bounded tail for the finite-matrix trace expansion;
        # the values themselves are evaluated in high-precision arithmetic.
        rho = inf_norm_A / ell
        assert rho < 1
        order = 100
        power_matrix = mp.eye(N)
        series = mp.mpf(0)
        for k in range(1, order + 1):
            power_matrix = power_matrix * (A / ell)
            series += trace(power_matrix) / k
        series_tail = N * rho ** (order + 1) / ((order + 1) * (1 - rho))
        assert abs(ideal_loss - series) < series_tail + ROUNDING_ALLOWANCE
        matrix_rows.append({
            "h": h_text, "ell": decimal(ell),
            "max_abs_ell_I_minus_R_minus_A": decimal(approximation_error),
            "det_R": decimal(det_R), "negative_logdet_R": decimal(loss),
            "ell_squared_times_negative_logdet_R": decimal(ell ** 2 * loss),
            "S2_limit": decimal(S2),
            "ell_cubed_times_cubic_remainder": decimal(ell ** 3 * (loss - S2 / ell ** 2)),
            "S3_limit": decimal(S3),
            "difference_from_ideal_matrix_logdet": decimal(loss - ideal_loss),
            "trace_series_order": order,
            "trace_series_tail_bound": decimal(series_tail),
            "trace_series_actual_discrepancy": decimal(abs(ideal_loss - series)),
        })
        for u_text, v_text in pair_values:
            u, v = mp.mpf(u_text), mp.mpf(v_text)
            B = brownian_kernel(u, v)
            diag = increment_covariance(mp.mpf(0), h, u, v)
            correction = (flog(u - v) - flog(u) - flog(v)) / 2
            diag_error = diag / h - ell * B - correction
            assert abs(diag_error) < 100 * h * (1 + L)
            cross = increment_covariance(mp.log(2), h, u, v)
            J = mp.log(2) / mp.sqrt(2)
            cross_error = cross / h + J * B
            assert abs(cross_error) < 100 * h
            negative = increment_covariance(mp.log(6), h, u, v)
            assert abs(negative / h) < 100 * h
            general_rows.append({
                "h": h_text, "u": u_text, "v": v_text,
                "Brownian_kernel": decimal(B),
                "diagonal_covariance_over_h_log_1_over_h": decimal(diag / (h * L)),
                "diagonal_first_correction": decimal(correction),
                "corrected_diagonal_error_over_h": decimal(diag_error),
                "log2_cross_covariance_over_h": decimal(cross / h),
                "log2_cross_limit": decimal(-J * B),
                "log2_cross_error": decimal(cross_error),
                "log6_negative_control_covariance_over_h": decimal(negative / h),
            })

    triangular_rows = []
    J = mp.log(2) / mp.sqrt(2)
    for h_text in ("1e-8", "1e-12"):
        h = mp.mpf(h_text)
        for v_text in ("-1.5", "-1", "-0.5", "0", "0.5", "1", "1.5"):
            v = mp.mpf(v_text)
            value = centered_second_difference(mp.log(2) + v * h, h) / h
            target = -J * max(mp.mpf(0), 1 - abs(v))
            assert abs(value - target) < 100 * h
            triangular_rows.append({"h": h_text, "v": v_text,
                                    "value": decimal(value), "triangular_limit": decimal(target),
                                    "error": decimal(value - target)})

    result = {
        "status": "all finite checks passed",
        "scope": "Exact finite combinatorial identities and 90-digit numerical asymptotic checks; not a proof or interval certificate.",
        "precision_decimal_digits": mp.mp.dps,
        "matrix_size": N,
        "index_set": list(range(1, N + 1)),
        "constants": {"K0": decimal(K0), "d": decimal(D),
                      "S2_trace_A_squared_over_2": decimal(S2),
                      "S3_trace_A_cubed_over_3": decimal(S3)},
        "arithmetic_matrix": [[decimal(A[i, j]) for j in range(N)] for i in range(N)],
        "trace_formula_checks": formal_trace_checks(N),
        "real_character_gauge_checks": exact_gauge_checks(N),
        "trivial_zero_tail_formula_checks": check_tail_formula(),
        "variance_checks": diagonal_rows,
        "correlation_matrix_checks": matrix_rows,
        "general_increment_covariance_checks": general_rows,
        "triangular_profile_checks": triangular_rows,
        "assertion_tolerances": {
            "algebraic_identity_absolute": decimal(ROUNDING_ALLOWANCE),
            "variance_remainder": "10 h^2",
            "matrix_first_order": "50 h (1 + log(1/h))",
            "matrix_logdet_perturbation": "100 h / ell",
            "corrected_diagonal_covariance": "100 h (1 + log(1/h))",
            "cross_covariance_and_triangle": "100 h",
            "explanation": "Conservative deterministic numerical thresholds for the displayed finite examples; the manuscript supplies proofs for the limiting statements.",
        },
    }
    destination = Path(__file__).resolve().parents[1] / "results" / "verification.json"
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(f"All checks passed at {mp.mp.dps} decimal digits; N={N}.")
    print(f"S2 = {decimal(S2, 24)}; S3 = {decimal(S3, 24)}")
    for row in matrix_rows:
        print("h={h}: matrix error {err}; ell^2 loss={q}; cubic scaled remainder={c}".format(
            h=row["h"], err=mp.nstr(mp.mpf(row["max_abs_ell_I_minus_R_minus_A"]), 6),
            q=mp.nstr(mp.mpf(row["ell_squared_times_negative_logdet_R"]), 12),
            c=mp.nstr(mp.mpf(row["ell_cubed_times_cubic_remainder"]), 12)))
    print(f"Wrote {destination}")


if __name__ == "__main__":
    main()
