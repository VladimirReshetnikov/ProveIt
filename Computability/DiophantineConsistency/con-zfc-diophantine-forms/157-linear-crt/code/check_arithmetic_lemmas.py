#!/usr/bin/env python3
"""Finite independent diagnostics for the new arithmetic lemmas.

These checks do not prove an unbounded consistency equivalence. The ordinary
proofs are in PARITY_BOOTSTRAP_LINEAR_RADIUS_PROOF.md. Standard library only.
"""
import itertools
import json
import math


def require(ok, description):
    if not ok:
        raise ValueError(description)


def prime_factors(n):
    out = {}
    p = 2
    while p * p <= n:
        while n % p == 0:
            out[p] = out.get(p, 0) + 1
            n //= p
        p += 1
    if n > 1:
        out[n] = out.get(n, 0) + 1
    return out


def coefficients(labels):
    out = [1]
    for j in labels:
        nxt = [0] * (len(out) + 1)
        for k, a in enumerate(out):
            nxt[k] += a
            nxt[k + 1] += j * a
        out = nxt
    return out


def main():
    counts = {}
    lcms = [1]
    for n in range(1, 401):
        lcms.append(math.lcm(lcms[-1], n))
        require(lcms[n] <= 4 ** (n - 1), f"LCM bound at {n}")
    for n in range(1, 200):
        require(lcms[n] * math.comb(2*n, n) % lcms[2*n] == 0,
                f"even LCM divisibility at {n}")
        require(lcms[n+1] * math.comb(2*n+1, n) % lcms[2*n+1] == 0,
                f"odd LCM divisibility at {n}")
        require(math.comb(2*n+1, n) <= 4**n,
                f"odd middle binomial bound at {n}")
    counts["lcm_bound_values"] = 400
    counts["lcm_divisibility_pairs"] = 199

    coefficient_cases = 0
    product_cases = 0
    for t in range(2, 7):
        for m in range(t + 1):
            for labels in itertools.combinations_with_replacement(range(1, t+1), m):
                cs = coefficients(labels)
                require(all(1 <= a <= t**m for a in cs),
                        f"coefficient bound at {t}, {labels}")
                coefficient_cases += 1
    for t in range(2, 5):
        f = t**t
        seen = {}
        for m in range(2*t + 2):
            for labels in itertools.combinations_with_replacement(range(1, t+1), m):
                value = math.prod(1 + j*f for j in labels)
                prior = seen.get(value)
                if prior is not None and min(m, len(prior)) <= t:
                    require(prior == labels,
                            f"label multiplicity collision at {t}, {labels}, {prior}")
                seen[value] = labels
                product_cases += 1
    counts["label_coefficient_cases"] = coefficient_cases
    counts["label_multiset_evaluations"] = product_cases

    # Full prime powers in B are computed from numerator/denominator factors,
    # independently of the binomial integer calculation.
    selector_rows = 0
    support_primes = 0
    for t in range(2, 8):
        f = t**t
        r = f
        b = math.comb(r+t, t)
        fs = {}
        for i in range(1, t+1):
            for p, e in prime_factors(r+i).items():
                fs[p] = fs.get(p, 0) + e
            for p, e in prime_factors(i).items():
                fs[p] = fs.get(p, 0) - e
        require(all(e >= 0 for e in fs.values()), "negative binomial valuation")
        powers = [p**e for p, e in fs.items() if e]
        require(math.prod(powers) == b, "independent binomial factorization")
        for i in range(1, t+1):
            require(any(pe > t and (r+i) % pe == 0 for pe in powers),
                    f"missing row selector at {t}, row {i}")
            selector_rows += 1
        for pe in powers:
            require(any((r+i) % pe == 0 for i in range(1, t+1)),
                    f"missing full-support assignment at {t}, prime power {pe}")
            support_primes += 1
        if t % 2 == 0:
            require(b % 2 == 1, "even-horizon binomial must be odd")
    counts["linear_radius_selector_rows"] = selector_rows
    counts["linear_radius_supported_prime_powers"] = support_primes

    # Explicit diagnostics for excluded shortcuts.
    require((1 + 3*1) == (1 + 1*1)**2,
            "small-evaluation multiplicity counterexample")
    t, r = 2, 1
    b = math.comb(r+t, t)
    powers = [p**e for p, e in prime_factors(b).items()]
    require(not any(pe > t and (r+1) % pe == 0 for pe in powers),
            "too-small CRT radius must lose its first selector")
    counts["negative_controls"] = 2

    for t in range(16, 81, 4):
        f = t**t
        require(f > 16**(t-1) >= lcms[t]**2, "linear radius size")
        require(f > 2**32 and f % 2 == 0, "growth and parity")
        for odd in (-5, -3, -1, 1, 3, 5):
            y = f * odd
            require(abs(y) >= f, "affine beta nonzero bound")
            require(abs(1 + (t+1)*y) > 1, "exclude zero beta exponent")
            if y + 1 >= 0:
                require(y >= f, "signed-index beta sign recovery")
    counts["affine_beta_scalar_cases"] = 17 * 6

    print(json.dumps({"status": "PASS", "checks": counts,
                      "scope": "Finite transcription/corner-case diagnostics; ordinary proofs remain essential"},
                     indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
