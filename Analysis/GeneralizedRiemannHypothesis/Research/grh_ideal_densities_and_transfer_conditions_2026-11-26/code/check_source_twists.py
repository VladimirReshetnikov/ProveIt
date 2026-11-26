#!/usr/bin/env python3
"""Exact finite certificates for tame twists over Q(sqrt(-23)).

No external packages.  Every primality decision in a search is certified by
an Eratosthenes sieve of the arithmetic progression.  All residue operations
are integer operations.  The mathematical class-field reduction is proved in
source_twists.tex; this program verifies the finite arithmetic part only.
"""
from __future__ import annotations

import csv
import json
import math
from pathlib import Path


def primes_up_to(n: int) -> list[int]:
    a = bytearray(b"\x01") * (n + 1)
    if n >= 0:
        a[0] = 0
    if n >= 1:
        a[1] = 0
    for p in range(2, math.isqrt(n) + 1):
        if a[p]:
            a[p * p::p] = b"\x00" * ((n - p * p) // p + 1)
    return [i for i in range(2, n + 1) if a[i]]


def progression_primes(k: int, bound: int) -> list[int]:
    """All primes q<=bound with q=1 mod k, proved by a progression sieve."""
    stop = (bound - 1) // k
    flags = bytearray(b"\x01") * (stop + 1)
    flags[0] = 0  # k*0+1=1 is not prime.
    for r in primes_up_to(math.isqrt(bound)):
        if k % r == 0:
            continue
        first = (-pow(k, -1, r)) % r
        if first <= stop:
            flags[first::r] = b"\x00" * ((stop - first) // r + 1)
        # The sieve marks q=r itself; preserve that prime.
        if (r - 1) % k == 0:
            flags[(r - 1) // k] = 1
    return [k * n + 1 for n in range(1, stop + 1) if flags[n]]


def v3(n: int) -> int:
    assert n > 0
    v = 0
    while n % 3 == 0:
        n //= 3
        v += 1
    return v


def split(q: int) -> bool:
    return q != 23 and pow(-23 % q, (q - 1) // 2, q) == 1


def sqrt_mod(a: int, q: int) -> int:
    """Tonelli--Shanks, returning the smaller of the two square roots."""
    a %= q
    assert q % 2 == 1 and a != 0 and pow(a, (q - 1) // 2, q) == 1
    if q % 4 == 3:
        x = pow(a, (q + 1) // 4, q)
    else:
        s, d = 0, q - 1
        while d % 2 == 0:
            d //= 2
            s += 1
        z = 2
        while pow(z, (q - 1) // 2, q) != q - 1:
            z += 1
        c, x, t, m = pow(z, d, q), pow(a, (d + 1) // 2, q), pow(a, d, q), s
        while t != 1:
            i, t2 = 0, t
            while t2 != 1:
                t2 = t2 * t2 % q
                i += 1
            assert 0 < i < m
            b = pow(c, 1 << (m - i - 1), q)
            x = x * b % q
            c = b * b % q
            t = t * c % q
            m = i
    assert x * x % q == a
    return min(x, q - x)


def strong_ok(q: int, n: int) -> bool:
    k = 3**n
    if (q - 1) % k or not split(q):
        return False
    e = (q - 1) // k
    if pow(3, e, q) != 1:
        return False
    return pow((2 + sqrt_mod(-23, q)) % q, e, q) == 1


def weak_ok(q: int, n: int) -> bool:
    k = 3**n
    if (q - 1) % k or not split(q):
        return False
    r = sqrt_mod(-23, q)
    u = (2 + r) * pow((2 - r) % q, -1, q) % q
    return pow(u, (q - 1) // k, q) == 1


def relation_vector(q: int) -> dict:
    """Coordinates of 3 and beta in the cyclic local 3-group."""
    h = v3(q - 1)
    m = (q - 1) // 3**h
    a = 2
    while pow(a, (q - 1) // 3, q) == 1:
        a += 1
    zeta = pow(a, m, q)
    powers = {}
    z = 1
    for j in range(3**h):
        assert z not in powers
        powers[z] = j
        z = z * zeta % q
    assert z == 1 and len(powers) == 3**h
    root = sqrt_mod(-23, q)
    beta = (2 + root) % q
    d3 = powers[pow(3, m, q)]
    db = powers[pow(beta, m, q)]
    # Multiplying all coordinates in a column by a 3-adic unit changes
    # neither the quotient nor its elementary divisors.
    return {"q": q, "h": h, "sqrt_minus23": root, "beta": beta,
            "generator": zeta, "cofactor": m, "log3": d3, "logbeta": db}


def max_order_exponent(q: int, strong: bool) -> int:
    h = v3(q - 1)
    predicate = strong_ok if strong else weak_ok
    return max([0] + [n for n in range(1, h + 1) if predicate(q, n)])


def first_eligible(n: int, how_many: int = 3) -> list[int]:
    bound = 3**n * 100
    while True:
        ans = [q for q in progression_primes(3**n, bound) if split(q)]
        if len(ans) >= how_many:
            return ans[:how_many]
        bound *= 4


def verify_rows(expected: list[int], strong: bool) -> list[dict]:
    rows = []
    predicate = strong_ok if strong else weak_ok
    for n, bound in enumerate(expected, 1):
        candidates = progression_primes(3**n, bound)
        successes = [q for q in candidates if predicate(q, n)]
        assert successes == [bound], (strong, n, successes)
        hmax = max_order_exponent(bound, strong)
        count = sum(2 * 3**(j - 1) for j in range(n, hmax + 1))
        row = {"N": n, "epsilon_denominator": 3**(n - 1), "q_min": bound,
               "conductor_norm": bound * bound,
               "max_local_order_exponent": hmax,
               "number_of_outputs_at_minimum": count,
               "number_of_progression_primes_checked": len(candidates),
               "relation": relation_vector(bound)}
        eligible = first_eligible(n + 1)
        row["first_eligible_primes_for_two_or_more_pairs"] = eligible
        if eligible[0] * eligible[1] > bound:
            row["multipair_exclusion"] = "product_of_two_smallest_eligible_primes_exceeds_single_support_minimum"
        else:
            # The only nontrivial case in the asserted table.
            assert strong and n == 4
            assert eligible[0] ** 3 > bound
            assert eligible[1] ** 2 > bound
            q1 = eligible[0]
            possible_q2 = [q for q in progression_primes(3**(n + 1), (bound - 1) // q1)
                           if q > q1 and split(q)]
            assert possible_q2 == [3889, 4861, 8263, 19441, 19927]
            r1 = relation_vector(q1)
            assert r1["h"] == 5
            certificates = []
            for q2 in possible_q2:
                r2 = relation_vector(q2)
                assert r2["h"] == 5
                d1, b1 = r1["log3"] % 3, r1["logbeta"] % 3
                d2, b2 = r2["log3"] % 3, r2["logbeta"] % 3
                determinants = [(d1 * sign * b2 - b1 * d2) % 3 for sign in [1, -1]]
                assert all(determinants)
                certificates.append({"q1": q1, "q2": q2,
                                     "support_product": q1 * q2,
                                     "relation_mod3_q1": [d1, b1],
                                     "relation_mod3_q2": [d2, b2],
                                     "determinants_for_both_orientations": determinants})
            row["multipair_exclusion"] = certificates
        rows.append(row)
        scope = "strong" if strong else "weak"
        print(f"PASS {scope}: N={n}, q={bound}, norm={bound*bound}, "
              f"local quotient C_(3^{hmax}), outputs={count}, "
              f"sieved primes={len(candidates)}")
    return rows


def self_check() -> None:
    # Cross-check progression sieves against a full classical sieve.
    ordinary = set(primes_up_to(10000))
    for k in [3, 9, 27, 81, 243, 729]:
        assert progression_primes(k, 10000) == sorted(q for q in ordinary if q % k == 1)
    # Independently brute-force square roots at every small odd prime.
    for q in primes_up_to(500):
        if q == 2:
            continue
        for a in {x * x % q for x in range(1, q)}:
            r = sqrt_mod(a, q)
            assert r == min(x for x in range(q) if x * x % q == a)
    print("PASS independent sieve and square-root checks")


def main() -> None:
    self_check()
    strong = verify_rows([151, 6481, 6481, 11767033, 102906613], True)
    weak = verify_rows([151, 541, 6481, 94447, 238627, 1573183], False)
    # Explicit distinction: q=541 works for the output character but not
    # for a precursor supported on one prime and trivial above 3.
    assert weak_ok(541, 2) and not strong_ok(541, 2)
    output = Path(__file__).resolve().parents[1] / "data"
    output.mkdir(exist_ok=True)
    result = {"field_discriminant": -23, "coefficient_prime": 3,
              "valuation_normalization": "v_3(3)=1",
              "strong_scope": "psi=xi/xi^c; xi tame on one prime from each split pair, trivial on both decomposition groups above 3",
              "weak_scope": "psi anticyclotomic, tame on split pairs, trivial on decomposition groups above 3",
              "strong_rows": strong, "weak_rows": weak}
    (output / "source_twist_certificate.json").write_text(json.dumps(result, indent=2) + "\n")
    with (output / "source_twist_minima.csv").open("w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["scope", "N", "epsilon_denominator", "q_min", "conductor_norm",
                    "max_local_order_exponent", "number_of_outputs_at_minimum"])
        for scope, rows in [("strong", strong), ("weak", weak)]:
            for r in rows:
                w.writerow([scope] + [r[k] for k in ["N", "epsilon_denominator", "q_min",
                    "conductor_norm", "max_local_order_exponent", "number_of_outputs_at_minimum"]])
    print("PASS all exact minima, including every smaller multiprime support")
    print("Certificates written to data/source_twist_certificate.json and data/source_twist_minima.csv")


if __name__ == "__main__":
    main()
