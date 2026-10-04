#!/usr/bin/env python3
"""Exact, deterministic corroboration for the Jacobi addendum.

No upstream program or saved arithmetic schedule is executed. Default output is
canonical JSON on stdout. --expect compares frozen bytes. --output creates a new
file outside this packet. All checks survive Python -O.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
from math import gcd, isqrt
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
PARENT_MANIFEST_SHA256 = "b769c58935f5951b1ad4b23df0daa5a9c31e2a04ea734d7bb9916249e51e9c38"


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def jacobi(a, n):
    require(n > 0 and n % 2 == 1, "Jacobi denominator must be positive odd")
    a %= n
    sign = 1
    while a:
        while a % 2 == 0:
            a //= 2
            if n % 8 in (3, 5):
                sign = -sign
        a, n = n, a
        if a % 4 == 3 and n % 4 == 3:
            sign = -sign
        a %= n
    return sign if n == 1 else 0


def trial_factors(n):
    require(n > 0 and n % 2 == 1, "Oracle denominator must be positive odd")
    result = []
    divisor = 3
    while divisor * divisor <= n:
        power = 0
        while n % divisor == 0:
            n //= divisor
            power += 1
        if power:
            result.append((divisor, power))
        divisor += 2
    if n > 1:
        result.append((n, 1))
    return result


def factored_jacobi(a, factors):
    result = 1
    for prime, power in factors:
        residue = a % prime
        if residue == 0:
            return 0
        euler = pow(residue, (prime - 1) // 2, prime)
        require(euler in (1, prime - 1), "Euler oracle encountered a nonprime")
        result *= (1 if euler == 1 else -1) ** power
    return result


def oracle_crosscheck():
    count = composite = 0
    for n in range(1, 202, 2):
        factors = trial_factors(n)
        is_composite = n > 1 and (len(factors) > 1 or factors[0][1] > 1)
        for a in range(-3, 206):
            require(jacobi(a, n) == factored_jacobi(a, factors), "Jacobi/oracle disagreement")
            count += 1
            composite += int(is_composite)
    return {"comparisons": count, "composite_denominator_comparisons": composite,
            "denominators": "all odd n from 1 through 201",
            "numerators": "all integers from -3 through 205"}


def general_filter_fixtures():
    q_values = (4, 16, 64, 100, 196, 256, 400, 484)
    counts = {"minus_one": 0, "zero": 0, "plus_one": 0}
    even_w = odd_power_checks = exclusions = 0
    powers = (1, 3, 13, 101, 1001)
    for q in q_values:
        require(q % 2 == 0 and isqrt(q) ** 2 == q and q % 3, "Bad fixture q")
        h0 = 4 * q ** 3 + 3
        w_values = set(range(1, 258))
        w_values.update(2 ** nu for nu in range(1, 16))
        w_values.update(h0 * k + delta for k in range(1, 10) for delta in (-1, 0, 1))
        for w in sorted(w_values):
            X = q ** 3 * w
            H = 4 * q ** 6 * w + h0
            require(H % 8 == h0 % 8 == 3, "Supplementary residue failure")
            require(gcd(q, H) == 1, "Square multiplier not coprime")
            require(gcd(w, H) == gcd(w, h0), "GCD identity failure")
            require(jacobi(q ** 3, H) == 1, "Square multiplier character failure")
            symbol = jacobi(w, h0)
            require(jacobi(X, H) == symbol, "Fixed-modulus identity failure")
            counts[{-1: "minus_one", 0: "zero", 1: "plus_one"}[symbol]] += 1
            even_w += int(w % 2 == 0)
            for p in powers:
                residue = pow(2, p, H)
                require(jacobi(residue, H) == -1, "Odd exponent character failure")
                odd_power_checks += 1
                if symbol != -1:
                    require((residue - X) % H != 0, "Excluded character produced a hit")
                    exclusions += 1
    require(all(counts.values()), "Missing character class coverage")
    return {"q_values": list(q_values), "w_cases_by_symbol": counts,
            "even_w_cases": even_w, "odd_exponent_checks": odd_power_checks,
            "exact_modular_exclusions": exclusions,
            "scope": "Abstract arithmetic fixtures, not genuine compiler/Pell-ratio tuples"}


def thinning_fixtures():
    count = even_w = 0
    for q in (4, 16, 64, 100, 196, 256, 400, 484):
        h0 = 4 * q ** 3 + 3
        for multiple in (1, 4):
            T = multiple * h0
            for j in range(1, 25):
                w = 1 + (q - 1) * T * j
                H = 4 * q ** 6 * w + h0
                X = q ** 3 * w
                require(w % h0 == 1 and gcd(w, H) == 1, "Thinning coprimality failure")
                require(jacobi(X, H) == jacobi(w, h0) == 1, "Thinning character failure")
                if multiple == 4:
                    require(w % (4 * h0) == 1, "Original thinning residue failure")
                    chain = (jacobi(w, H), jacobi(H, w), jacobi(h0, w), jacobi(w, h0))
                    require(chain == (1, 1, 1, 1), "Direct reciprocity chain failure")
                else:
                    even_w += int(w % 2 == 0)
                for p in (1, 3, 13, 101, 1001):
                    require(0 < (pow(2, p, H) - X) % H < H, "Thinned residue was zero")
                count += 1
    require(even_w > 0, "Stronger thinning did not exercise even w")
    # A family denominator that is composite, checked by a second implementation.
    q = 4
    h0 = 4 * q ** 3 + 3
    w = 1 + (q - 1) * 4 * h0
    H = 4 * q ** 6 * w + h0
    factors = trial_factors(H)
    require(len(factors) > 1 or factors[0][1] > 1, "Expected composite fixture")
    require(factored_jacobi(q ** 3 * w, factors) == 1, "Composite numerator oracle failure")
    require(factored_jacobi(2, factors) == -1, "Composite supplement oracle failure")
    return {"thinned_cases": count, "even_w_cases_in_T_h0": even_w,
            "composite_family_denominator": H, "composite_factorization": factors}


def structural_compiler_bounds():
    count = 0
    for d_cell, b in ((5, 1), (5, 5), (25, 1), (25, 5), (25, 25), (125, 25)):
        for x in (1, 2, 3):
            B = 2 ** d_cell
            u = 2 * d_cell * x + b
            W = 2 ** u
            q = B ** (2 * x + 2)
            require(q == (B ** (x + 1)) ** 2, "Explicit q is not the claimed square")
            require(q % 2 == 0 and q % 3 and q % (B - 1) == 1, "q congruence failure")
            require(q >= W + u - b + 2, "Positive input marker bound failure")
            h0 = 4 * q ** 3 + 3
            for T in (h0, 4 * h0):
                for j in (1, 2):
                    w = 1 + (q - 1) * T * j
                    H = 4 * q ** 6 * w + h0
                    require(jacobi(q ** 3 * w, H) == 1, "Large structural fixture failure")
            count += 1
    return {"structural_cases": count,
            "scope": "Exponent/loading structure only; no compiler masks or full witness materialized"}


def formal_scaling_and_residual_checks():
    chain_cases = count_cases = residual_cases = 0
    for T in (1, 3, 259, 1036):
        for K in (Fraction(1, 3), Fraction(7, 5), Fraction(41, 2)):
            for j in (1, 2, 17):
                for ell in (Fraction(1, 2), Fraction(3), Fraction(19, 4)):
                    left = T ** 2 * (-K / (T * j * ell ** 2))
                    right = -K * T / (j * ell ** 2)
                    require(left == right, "Exact chain scaling factor failure")
                    chain_cases += 1
    for delta in (Fraction(1, 9), Fraction(2, 11), Fraction(1, 10 ** 12)):
        for L0 in (2, 180, 10 ** 12):
            kappa = delta / (8 * L0)
            require(kappa / 4 == delta / (32 * L0), "Density lower constant failure")
            count_cases += 1
    for Dpell in (10, 31, 10 ** 10):
        for rho in (1, 2, 7):
            require(rho < Dpell, "Bad residual fixture")
            diff = (Dpell - rho) ** 2 - Dpell ** 2
            require(diff == -rho * (2 * Dpell - rho), "Eliminated norm residual failure")
            require(rho ** 2 > 0 and diff ** 2 > 0, "Residual positivity failure")
            residual_cases += 1
    return {"exact_chain_factor_cases": chain_cases, "density_constant_cases": count_cases,
            "positive_residual_identity_cases": residual_cases,
            "scope": "Exact algebra only; asymptotic bounds and existence are proved in the notes"}


def boundary_controls():
    # A nonsquare q cannot silently use the square multiplier argument.
    q = 2
    h0 = 4 * q ** 3 + 3
    w = 1 + (q - 1) * 4 * h0
    H = 4 * q ** 6 * w + h0
    require(jacobi(w, h0) == 1 and jacobi(q ** 3 * w, H) == -1,
            "Nonsquare control did not distinguish the hypotheses")
    # Even exponents do not have the obstructing character.
    require(jacobi(pow(2, 2, H), H) == 1, "Even-exponent control failed")
    # If 3 divides q, the square multiplier need not be coprime to H.
    q_bad = 36
    H_bad = 4 * q_bad ** 6 + 4 * q_bad ** 3 + 3
    require(gcd(q_bad, H_bad) == 3 and jacobi(q_bad ** 3, H_bad) == 0,
            "Divisibility-by-three control failed")
    return {"controls": ["nonsquare q changes multiplier character", "even p has character +1",
                         "3 dividing q destroys coprimality"]}


def authenticate_context():
    parent = ROOT / "inherited-family"
    manifest = parent / "MANIFEST.sha256"
    require(sha(manifest) == PARENT_MANIFEST_SHA256, "Inherited manifest pin mismatch")
    count = 0
    for line in manifest.read_text().splitlines():
        digest, name = line.split("  ", 1)
        target = (parent / name).resolve()
        require(target.is_relative_to(parent.resolve()), "Manifest target escaped inherited packet")
        require(sha(target) == digest, "Inherited file mismatch: " + name)
        count += 1
    provenance = json.loads((ROOT / "source_manifest.json").read_text())
    require(provenance["inherited_manifest_sha256"] == PARENT_MANIFEST_SHA256,
            "Provenance inherited manifest mismatch")
    for name, expected in provenance["root_proposal"].items():
        require(sha(ROOT / "context" / name) == expected, "Historical root proposal mismatch")
    return {"inherited_files_verified": count, "inherited_manifest_sha256": PARENT_MANIFEST_SHA256,
            "root_proposal_files_verified": len(provenance["root_proposal"])}


def build_receipt():
    return {"status": "PASS", "scope": "Exact corroboration plus frozen context authentication; no upstream execution",
            "oracle": oracle_crosscheck(), "fixed_modulus_filter": general_filter_fixtures(),
            "thinning": thinning_fixtures(), "structural_bounds": structural_compiler_bounds(),
            "formal_identities": formal_scaling_and_residual_checks(), "boundary_controls": boundary_controls(),
            "context": authenticate_context(),
            "hashes": {name: sha(ROOT / name) for name in
                       ("JACOBI-ADDENDUM.md", "INDEPENDENT-AUDIT.md", "check_jacobi_addendum.py", "source_manifest.json")},
            "limitations": ["No genuine compiler tuple materialized", "Finite tests do not establish analytic existence",
                            "No main-congruence hit or global sign theorem claimed"]}


def canonical_bytes(receipt):
    return (json.dumps(receipt, sort_keys=True, indent=2) + "\n").encode()


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--expect", type=Path, help="Compare receipt byte-for-byte with this frozen JSON")
    parser.add_argument("--output", type=Path, help="Create a new receipt outside this packet")
    args = parser.parse_args(argv)
    if args.output is not None:
        target = args.output.resolve()
        require(not target.is_relative_to(ROOT), "--output must be outside packet")
        require(not target.exists(), "--output must not overwrite an existing file")
        require(args.expect is None or target != args.expect.resolve(), "--output must not overwrite --expect")
    data = canonical_bytes(build_receipt())
    if args.expect is not None:
        require(args.expect.read_bytes() == data, "Frozen receipt mismatch")
    if args.output is None:
        sys.stdout.buffer.write(data)
    else:
        with target.open("xb") as stream:
            stream.write(data)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
