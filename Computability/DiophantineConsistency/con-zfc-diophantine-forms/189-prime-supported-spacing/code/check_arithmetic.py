"""Finite independent regressions for the prime-index Pell audit.

These checks support debugging of the finite constants and congruence
interfaces. They do not replace the unbounded proof in audit_alternative.md.
Python standard library only; no producer imports.
"""

import json
from math import gcd, isqrt, lcm


def primes_up_to(bound):
    mark = bytearray(b"\x01") * (bound + 1)
    mark[:2] = b"\x00\x00"
    for p in range(2, isqrt(bound) + 1):
        if mark[p]:
            mark[p * p : bound + 1 : p] = b"\x00" * (
                (bound - p * p) // p + 1
            )
    return [p for p in range(2, bound + 1) if mark[p]]


def pair_mul(left, right, delta, modulus):
    x, y = left
    u, v = right
    return ((x * u + delta * y * v) % modulus,
            (x * v + y * u) % modulus)


def pair_pow(base, exponent, delta, modulus):
    result = (1, 0)
    while exponent:
        if exponent & 1:
            result = pair_mul(result, base, delta, modulus)
        base = pair_mul(base, base, delta, modulus)
        exponent >>= 1
    return result


def zero_rank_bound(a, p):
    if p == 2:
        return 2
    delta = a * a - 1
    if delta % p == 0:
        return p
    symbol = pow(delta, (p - 1) // 2, p)
    if symbol == p - 1:
        symbol = -1
    if symbol not in (-1, 1):
        raise ValueError("Euler criterion failure")
    return p - symbol


def check(condition, message):
    if not condition:
        raise AssertionError(message)


def main():
    literal_c = 524309
    trial_primes = primes_up_to(isqrt(literal_c))
    check(all(literal_c % p for p in trial_primes), "literal c is composite")
    check(literal_c > 2**19 + 1, "literal c is too small")

    rank_cases = 0
    ramified_cases = 0
    for a in range(2, 50):
        delta = a * a - 1
        for p in primes_up_to(101):
            rho = zero_rank_bound(a, p)
            check(1 <= rho <= p + 1, "rank bound")
            check(pair_pow((a % p, 1), rho, delta, p)[1] == 0,
                  "ordinate not zero")
            rank_cases += 1
            ramified_cases += (delta % p == 0)

    # A smaller prime is used only to make this finite CRT fixture cheap.
    # The analytic growth constant remains the literal c above.
    toy_c, k = 37, 1
    t = 32 * toy_c ** (2 * k)
    a = toy_c * t + 1
    ell = t.bit_length() + 3
    modulus = 2**ell
    ranks = []
    for p in primes_up_to(t):
        rho = zero_rank_bound(a, p)
        check(rho < toy_c ** (2 * k + 1), "cofinal rank bound")
        ranks.append(rho)
        modulus = lcm(modulus, rho)
    front_modulus = toy_c * t
    common = gcd(modulus, front_modulus)
    check(t % common == 0, "CRT incompatibility")
    reduced = front_modulus // common
    factor = (-t // common) * pow(modulus // common, -1, reduced) % reduced
    n = modulus * factor
    if n <= 0:
        n += lcm(modulus, front_modulus)
    check(n > 0 and n % modulus == 0, "rank multiple")
    check((n + t) % front_modulus == 0, "growth index congruence")
    check(all(n % rho == 0 for rho in ranks), "missing prime rank")
    check(n % (2**ell) == 0, "missing binary divisibility")
    check(pair_pow((a % front_modulus, 1), n, a * a - 1,
                   front_modulus)[1] == (-t) % front_modulus,
          "Pell ordinate congruence")

    print(json.dumps({
        "literal_prime": literal_c,
        "trial_divisors": len(trial_primes),
        "pell_rank_cases": rank_cases,
        "ramified_cases": ramified_cases,
        "cofinal_crt_fixture": {
            "prime": toy_c,
            "k": k,
            "t": t,
            "rank_count": len(ranks),
            "required_binary_valuation": ell,
            "index_bits": n.bit_length(),
            "gcd_divides_t": True,
        },
        "status": "all finite checks passed",
        "scope": "finite regression only; see the independent unbounded proof",
    }, indent=2))


if __name__ == "__main__":
    main()
