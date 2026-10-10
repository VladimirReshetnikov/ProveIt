#!/usr/bin/env python3
"""Exact independent polynomial checks and rational initial-velocity signs.

All proof-relevant arithmetic uses fractions.Fraction. Floating point is used
only for the human-readable diagnostic approximation at the end.
"""
from fractions import Fraction as Q
from math import factorial
import json


def trim(p):
    p = list(p)
    while len(p) > 1 and not p[-1]:
        p.pop()
    return p


def add(p, q):
    out = [Q(0)] * max(len(p), len(q))
    for j, a in enumerate(p):
        out[j] += a
    for j, a in enumerate(q):
        out[j] += a
    return trim(out)


def scale(p, a):
    return trim([a * x for x in p])


def multiply(p, q):
    out = [Q(0)] * (len(p) + len(q) - 1)
    for j, a in enumerate(p):
        for k, b in enumerate(q):
            out[j + k] += a * b
    return trim(out)


def stirling_table(nmax):
    c = [[0] * (nmax + 1) for _ in range(nmax + 1)]
    c[0][0] = 1
    for n in range(1, nmax + 1):
        for j in range(1, n + 1):
            c[n][j] = c[n - 1][j - 1] + (n - 1) * c[n - 1][j]
    return c


def interval_add(x, y):
    return x[0] + y[0], x[1] + y[1]


def interval_multiply(x, y):
    vals = [a * b for a in x for b in y]
    return min(vals), max(vals)


def evaluate_interval(p, x):
    out = (Q(0), Q(0))
    for a in reversed(p):
        out = interval_add(interval_multiply(out, x), (a, a))
    return out


def log2_interval(n):
    lo = 2 * sum((Q(1, (2*j + 1) * 3**(2*j + 1)) for j in range(n)), Q(0))
    err = Q(2, (2*n + 1) * 3**(2*n + 1)) / (1 - Q(1, 9))
    return lo, lo + err


def main():
    nmax = 40
    c = stirling_table(nmax)
    direct = {n: [Q(0)] + [Q((-1)**j * c[n][n-j+1], factorial(j))
                           for j in range(1, n+1)]
              for n in range(1, nmax+1)}
    recurrence = {1: [Q(0), Q(-1)]}
    for n in range(1, nmax):
        next_p = multiply([Q(n+1), Q(-n)], recurrence[n])
        for j in range(1, n):
            next_p = add(next_p, scale(multiply(recurrence[j], recurrence[n-j]), Q(n, 2)))
        recurrence[n+1] = scale(next_p, Q(1, n+1))
    for n in range(1, nmax+1):
        assert direct[n] == recurrence[n], (n, direct[n], recurrence[n])
        assert direct[n][0] == 0 and direct[n][1] == -1
        assert direct[n][-1] == Q((-1)**n, n)

    # Exact coefficient-by-coefficient check of the inverse equation:
    # exp(-V) = 1 + t*(L-V)/A, specialized to rational L=1/3 and A=2.
    # This is a formal check independent of the numerical value log(2).
    L = Q(1, 3)
    vals = [Q(0)]
    for n in range(1, nmax+1):
        v = evaluate_interval(direct[n], (L, L))[0] / 2**n
        vals.append(v)
    exp_neg_v = [Q(1)]
    for n in range(1, nmax+1):
        exp_neg_v.append(-sum(Q(j) * vals[j] * exp_neg_v[n-j]
                             for j in range(1, n+1)) / n)
    assert exp_neg_v[1] == L/2
    for n in range(2, nmax+1):
        assert exp_neg_v[n] == -vals[n-1]/2

    log_interval = log2_interval(80)
    rows = []
    for n in range(2, nmax+1):
        lo, hi = evaluate_interval(direct[n], log_interval)
        lo, hi = lo / 2**n, hi / 2**n
        assert lo * hi > 0, (n, lo, hi)
        decimal_scale = 10**40
        lower_integer = (lo * decimal_scale).numerator // (lo * decimal_scale).denominator
        upper_integer = -((-hi * decimal_scale).numerator // (-hi * decimal_scale).denominator)
        lo, hi = Q(lower_integer, decimal_scale), Q(upper_integer, decimal_scale)
        assert lo * hi > 0
        rows.append({"n": n, "k": n-1,
                     "sign": "+" if lo > 0 else "-",
                     "lower": str(lo), "upper": str(hi),
                     "diagnostic_midpoint": float((lo+hi)/2)})
    # A short independently reproducible positive-motion certificate.
    short_lo, short_hi = evaluate_interval(direct[4], log2_interval(20))
    short_lo, short_hi = short_lo/16, short_hi/16
    assert Q(1221096503, 10**11) < short_lo
    assert short_hi < Q(1221096504, 10**11)
    report = {"polynomial_checks": nmax,
              "inverse_equation_checks": nmax,
              "arithmetic": "exact rational",
              "n4_short_certificate": {"lower": str(short_lo), "upper": str(short_hi),
                                       "decimal_lower": "0.01221096503",
                                       "decimal_upper": "0.01221096504"},
              "initial_velocity_certificates": rows}
    from pathlib import Path
    output = Path(__file__).resolve().parents[1] / "data" / "diagonal_certificate.json"
    output.parent.mkdir(parents=True, exist_ok=True)
    with output.open("w") as out:
        json.dump(report, out, indent=2)
        out.write("\n")
    print(json.dumps({"polynomial_checks": nmax, "inverse_equation_checks": nmax,
                      "certified_signs": [{"n": r["n"], "sign": r["sign"]} for r in rows],
                      "n4_decimal_interval": ["0.01221096503", "0.01221096504"]}))


if __name__ == "__main__":
    main()
