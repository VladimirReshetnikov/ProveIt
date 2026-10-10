#!/usr/bin/env python3
"""Exact rational verification of the universal Euler theorem's finite claims.

Python standard library only. No float is used for an acceptance decision.
The analytic theorem in sections/euler.tex supplies the tail 5/4 * 2**(-N).
The 31 axis enclosures plus the proved Lipschitz bound 1/6 certify C_*<57/50.
"""
from fractions import Fraction as Q
from functools import lru_cache
from math import comb
from pathlib import Path
import argparse
import json


def floor_root(n, q):
    """Largest integer r with r**q <= n, using integer Newton iteration."""
    assert n >= 0 and q >= 1
    if n < 2 or q == 1:
        return n
    x = 1 << ((n.bit_length() + q - 1) // q)
    while True:
        y = ((q - 1) * x + n // pow(x, q - 1)) // q
        if y >= x:
            break
        x = y
    while pow(x + 1, q) <= n:
        x += 1
    while pow(x, q) > n:
        x -= 1
    assert pow(x, q) <= n < pow(x + 1, q)
    return x


@lru_cache(maxsize=None)
def reciprocal_power(n, exponent, places):
    """Outward rational interval for n**(-exponent), exponent nonnegative."""
    exponent = Q(exponent)
    assert n >= 1 and exponent >= 0
    if exponent.denominator == 1:
        value = Q(1, pow(n, exponent.numerator))
        return value, value
    p, q = exponent.numerator, exponent.denominator
    grid = 10 ** places
    top, denominator = pow(grid, q), pow(n, p)
    r = floor_root(top // denominator, q)
    assert pow(r, q) * denominator <= top
    if pow(r, q) * denominator == top:
        return Q(r, grid), Q(r, grid)
    assert top < pow(r + 1, q) * denominator
    return Q(r, grid), Q(r + 1, grid)


def euler_interval(a, b, N, places=55):
    """Enclose finite E_N by binomial-tail formula; all summands outward."""
    a, b = Q(a), Q(b)
    assert a >= 0 and b > 0 and N >= 1
    hs = [(Q(0), Q(0))]
    lo = hi = Q(0)
    for j in range(1, 2 * N - 1):
        lower, upper = reciprocal_power(j, b, places)
        lo, hi = lo + lower, hi + upper
        hs.append((lo, hi))
    tails = [0] * N
    running = 0
    for j in range(N, 0, -1):
        running += comb(N, j)
        tails[j - 1] = running
    low = high = Q(0)
    for n in range(1, N):
        pl, pu = reciprocal_power(2 * n + 1, a, places)
        fl, fu = hs[2 * n][0] * pl, hs[2 * n][1] * pu
        weight = Q(tails[n], 1 << N)
        if n % 2:
            low, high = low - weight * fu, high - weight * fl
        else:
            low, high = low + weight * fl, high + weight * fu
    return low, high


def gaussian_interval(a, b, N=96, places=65):
    low, high = euler_interval(a, b, N, places)
    return low - Q(5, 4 * (1 << N)), high


def interval_json(pair):
    return {"lower": str(pair[0]), "upper": str(pair[1])}


def W(N, x):
    return (1 - x) ** N / (1 + x)


def verify():
    kernel_cases = 0
    for N in range(1, 25):
        for ix in range(17):
            x = Q(ix, 16)
            for iv in range(1, 16):
                v = Q(iv, 16)
                difference = W(N, v * x) - W(N, x)
                bound = (1 - v) / (1 + v)
                assert 0 <= difference <= bound
                assert (difference == bound) == (N == 1 and x == 1)
                kernel_cases += 1

    axis = []
    grid_value_bound = Q(1137, 1000)
    for j in range(31):
        b = 1 + Q(j, 30)
        gl, gu = gaussian_interval(0, b, N=48, places=45)
        enclosure = (-2 * gu, -2 * gl)
        assert enclosure[1] < grid_value_bound
        axis.append({"b": str(b), "C_interval": interval_json(enclosure),
                     "upper_below_1137_over_1000": True})

    # The analytic maximum lies in (1,2). Every point there is within 1/60
    # of a node, and |C'|<1/6. The following strict comparison completes
    # the uniform rational bound, including all unbounded positive orders.
    uniform_upper = grid_value_bound + Q(1, 360)
    assert uniform_upper < Q(57, 50)

    cases = []
    for a, b in [(Q(1, 10), Q(9, 10)), (Q(1, 10), Q(1)),
                 (Q(1, 4), Q(1, 2)), (Q(1), Q(1)),
                 (Q(2), Q(3, 2)), (Q(7, 3), Q(2, 3))]:
        pair = gaussian_interval(a, b)
        cases.append({"a": str(a), "b": str(b), "g_interval": interval_json(pair)})
    # A deliberately too-small global constant is rejected at N=1.
    critical = gaussian_interval(Q(1, 10), Q(9, 10))
    assert critical[1] < -Q(13, 25) < -Q(1, 2)
    # A changed finite formula is rejected in a fully rational instance.
    exact_e2 = euler_interval(1, 1, 2)
    assert exact_e2 == (-Q(1, 8), -Q(1, 8))
    assert not (exact_e2[0] <= -Q(1, 7) <= exact_e2[1])

    return {"arithmetic": "Python int and fractions.Fraction only",
            "kernel_grid_cases": kernel_cases,
            "kernel_grid_is_not_a_proof_of_the_all_N_inequality": True,
            "axis_nodes": axis,
            "axis_N": 48, "axis_decimal_grid_places": 45,
            "analytic_lipschitz_bound": "1/6 on [1,2]",
            "certified_global_upper": str(uniform_upper),
            "simple_uniform_constant": "57/50",
            "gaussian_cases": cases,
            "rejected_controls": ["global constant 1", "E_2(1,1)=-1/7"],
            "status": "all exact assertions passed"}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", default="data/euler_exact_certificate.json")
    args = parser.parse_args()
    result = verify()
    path = Path(args.output)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({k: result[k] for k in ["kernel_grid_cases", "axis_N",
          "certified_global_upper", "simple_uniform_constant", "status"]}, indent=2))


if __name__ == "__main__":
    main()
