#!/usr/bin/env python3
"""Finite exact audits for the complementary-endpoint theorem.

The asymptotic bounds are proved in oeis_research.tex.
This script checks the algebraic identities used in that proof.
Python standard library only.
"""
import json


def coefficients(count):
    rows = [[1] * (count + 2)]
    for n in range(1, count + 1):
        row = [0] * (count + 2 - n)
        for k in range(1, len(row)):
            row[k] = row[k - 1] + sum(
                rows[i][k] * rows[n - 1 - i][k + 1]
                for i in range(n)
            )
        rows.append(row)
    return [rows[n][1] for n in range(count + 1)]


def mul(f, g, degree):
    h = [0] * (degree + 1)
    for i, fi in enumerate(f[:degree + 1]):
        for j, gj in enumerate(g[:degree + 1 - i]):
            h[i + j] += fi * gj
    return h


def power(f, exponent, degree):
    result = [1] + [0] * degree
    for _ in range(exponent):
        result = mul(result, f, degree)
    return result


def main():
    count = 32
    a = coefficients(count + 2)
    expected = [
        1, 1, 3, 13, 69, 419, 2809, 20353, 157199, 1281993, 10963825
    ]
    assert a[:len(expected)] == expected

    c = [1]
    for n in range(1, count + 2):
        c.append(sum(a[j] * c[n - 1 - j] for j in range(n)))
    assert c[:7] == [1, 1, 2, 6, 24, 118, 674]
    e = [sum(c[i] * c[h - i] for i in range(h + 1))
         for h in range(count + 1)]
    assert e[:6] == [1, 2, 5, 16, 64, 308]

    d = []
    for h in range(count + 1):
        d.append((h + 2) * a[h + 1] - sum(
            (i + 1) * a[i] * d[h - i] for i in range(1, h + 1)
        ))
        direct = sum(
            (k + 2) * a[k] * power(a, k + 1, h - k)[h - k]
            for k in range(h + 1)
        )
        assert d[h] == direct
        assert 0 < d[h] <= (h + 2) * a[h + 1]

    count_checks = 0
    for n in range(6, count + 1):
        N = n // 2
        H = n - N - 2
        terms = [
            a[k] * power(a, k + 2, n - 1 - k)[n - 1 - k]
            for k in range(n)
        ]
        assert sum(terms) == a[n]
        bounded = sum(
            a[k] * power(a[:N + 1], k + 2, n - 1 - k)[n - 1 - k]
            for k in range(N + 1)
        )
        unique_large = sum(d[h] * a[n - 1 - h] for h in range(H + 1))
        assert bounded + unique_large == sum(terms[:N + 1])
        companion_bounded = sum(
            power(a[:N + 1], k, n - k)[n - k]
            for k in range(1, n + 1)
        )
        companion_large = sum(e[h] * a[n - 1 - h]
                              for h in range(H + 1))
        assert c[n] == companion_bounded + companion_large
        for L in range(H):
            complement = sum(terms[:n - 1 - L])
            large_outer = sum(terms[N + 1:n - 1 - L])
            assert complement == large_outer + bounded + unique_large
            count_checks += 1

    print(json.dumps({
        "status": "passed",
        "max_sequence_index": len(a) - 1,
        "independent_coefficient_recurrence_checked_through": count,
        "endpoint_coefficient_identity_checked_through": count,
        "three_region_decompositions_checked": count_checks,
        "endpoint_coefficients_d_0_through_d_9": d[:10],
        "companion_coefficients_c_0_through_c_9": c[:10],
        "companion_endpoint_coefficients_e_0_through_e_9": e[:10],
        "companion_decompositions_checked": count - 5,
        "claims_not_tested": [
            "all-index inequalities beyond the written proof",
            "asymptotic error bounds",
            "Bell normalization or local curvature"
        ],
    }, indent=2))


if __name__ == "__main__":
    main()
