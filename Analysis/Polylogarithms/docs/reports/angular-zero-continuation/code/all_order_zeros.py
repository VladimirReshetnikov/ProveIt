"""Exact coefficients for the angular-zero exponential expansion.

Only finite asymptotic truncations are asserted.  This does not assert that
the infinite transseries converges at any fixed outer index.
Uses the decreasing-index convention Li_{a,b}(z,1).
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from fractions import Fraction as Q
from functools import lru_cache
from math import factorial
from pathlib import Path
import json
from package_io import read_json, write_json_new_or_compare


def mul(p, q, degree):
    out = [Q(0)] * (degree + 1)
    for i, x in enumerate(p):
        for j, y in enumerate(q[:degree + 1 - i]):
            out[i + j] += x * y
    return out


def power(p, k, degree):
    out = [Q(1)] + [Q(0)] * degree
    for _ in range(k):
        out = mul(out, p, degree)
    return out


def sine_mode(n, degree):
    """Taylor coefficients of sin(n*pi/2 - n*u)."""
    out = [Q(0)] * (degree + 1)
    for j in range(degree + 1):
        if n % 2 and j % 2 == 0:
            out[j] = Q((1 if n % 4 == 1 else -1)
                       * (-1)**(j // 2) * n**j, factorial(j))
        elif n % 2 == 0 and j % 2:
            out[j] = Q((1 if n % 4 == 2 else -1)
                       * (-1)**((j - 1) // 2) * n**j, factorial(j))
    return out


@lru_cache(None)
def inverse_sinc(degree):
    """Coefficients of u/sin(2u), including constant 1/2."""
    denominator = [Q(0)] * (degree + 1)
    for j in range(0, degree + 1, 2):
        denominator[j] = Q((-1)**(j // 2) * 2**(j + 1), factorial(j + 1))
    out = [Q(1, 2)] + [Q(0)] * degree
    for j in range(1, degree + 1):
        out[j] = -sum(denominator[k] * out[j - k]
                      for k in range(1, j + 1)) / 2
    return tuple(out)


@lru_cache(None)
def coefficient(modes):
    k = len(modes)
    if not k or sum(n % 2 for n in modes) % 2 == 0:
        return Q(0)
    degree = k - 1
    p = power(inverse_sinc(degree), k, degree)
    for n in modes:
        p = mul(p, sine_mode(n, degree), degree)
    den = 1
    for count in Counter(modes).values():
        den *= factorial(count)
    return Q((-1)**k * factorial(k - 1), den) * p[degree]


@lru_cache(None)
def scale(modes):
    result = Q(1)
    for n in modes:
        result *= Q(n, 2)
    return result


def enumerate_modes(cutoff, prefix=(), minimum=3, current=Q(1)):
    n = minimum
    while current * Q(n, 2) < cutoff:
        new = prefix + (n,)
        yield new
        yield from enumerate_modes(cutoff, new, n, current * Q(n, 2))
        n += 1


def expansion(cutoff):
    return {m: c for m in enumerate_modes(cutoff)
            if (c := coefficient(m))}


def formal_mul(left, right, cutoff):
    result = defaultdict(Q)
    for m, c in left.items():
        for n, d in right.items():
            t = tuple(sorted(m + n))
            if scale(t) < cutoff:
                result[t] += c * d
    return {m: c for m, c in result.items() if c}


def verify_formal(cutoff):
    """Independently substitute the Lagrange answer in the sine equation."""
    delta = expansion(cutoff)
    maxdegree = 0
    while Q(3, 2)**(maxdegree + 1) < cutoff:
        maxdegree += 1
    powers = [{(): Q(1)}]
    for _ in range(maxdegree):
        powers.append(formal_mul(powers[-1], delta, cutoff))
    residual = defaultdict(Q)
    for j in range(1, maxdegree + 1, 2):
        c = Q((-1)**((j - 1)//2) * 2**j, factorial(j))
        for m, v in powers[j].items():
            residual[m] += c * v
    for n in range(3, int(2 * cutoff) + 1):
        if Q(n, 2) >= cutoff:
            break
        mode = sine_mode(n, maxdegree)
        for j, c in enumerate(mode):
            if c:
                for m, v in powers[j].items():
                    t = tuple(sorted(m + (n,)))
                    if scale(t) < cutoff:
                        residual[t] += c * v
    nonzero = {m: str(c) for m, c in residual.items() if c}
    assert not nonzero, nonzero
    return {"cutoff": str(cutoff), "nonzero_coefficients": len(delta),
            "residual_coordinates_checked": len(residual),
            "all_residuals_exactly_zero": True}


def serialise(cutoff):
    groups = defaultdict(list)
    for modes, c in expansion(cutoff).items():
        groups[scale(modes)].append({"modes": list(modes), "coefficient": str(c)})
    return [{"scale": str(lam), "terms": groups[lam]}
            for lam in sorted(groups)]


def verify_reference():
    """Compare every stored coefficient and check the requested cutoff itself."""
    reference = read_json("zero_coefficients.json")
    cutoff = Q(reference["cutoff_exclusive"])
    assert serialise(cutoff) == reference["coefficients"], "Coefficient table changed"
    checks = []
    for expected in reference.get("exact_checks", []):
        actual = verify_formal(Q(expected["cutoff"]))
        assert actual == expected, "Stored formal-substitution receipt changed"
        checks.append(actual)
    if not any(Q(row["cutoff"]) == cutoff for row in checks):
        checks.append(verify_formal(cutoff))
    result = {"coefficient_table_matched": True, "cutoff_exclusive": str(cutoff),
              "scale_groups": len(reference["coefficients"]), "exact_checks": checks,
              "scope": "finite exact coefficients and substitution; analytic remainder is proved in the article"}
    print(json.dumps(result, indent=2))
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--cutoff", default="12")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    cutoff = Q(args.cutoff)
    data = {"definition": "delta = sum C_m prod(H_{n-1}^{(b)}) lambda_m^(-a)",
            "cutoff_exclusive": str(cutoff), "coefficients": serialise(cutoff),
            "exact_checks": [verify_formal(value) for value in sorted({Q(4), Q(8), cutoff})]}
    if args.output:
        write_json_new_or_compare(args.output, data)
    for row in data["coefficients"]:
        print(row)
    print(data["exact_checks"])


if __name__ == "__main__":
    main()
