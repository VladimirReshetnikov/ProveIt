#!/usr/bin/env python3
"""Independent, exact, standard-library-only audit of the frozen counting packet.

Usage: python3 check_independent.py /path/to/native-gap-counting-continuation-20261004
Reads source bytes only. Never imports or executes a packet script. Writes only
JSON to stdout; redirect stdout to a file outside the frozen source directories.
Finite checks supplement the companion independent mathematical review.
"""
import argparse
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from hashlib import sha256
from math import gcd, lcm
from pathlib import Path
import json


PROOF_SHA = "dbc5c8e1cc692f734eaf795a57d081af242469ad41fdcbcdbed0ab5324d55246"
MANIFEST_SHA = "0a660b083eb7c381eb3af1d31cb992dee3ccd2f77a0f473cffb062314aae4781"
DEPENDENCY_SHA = "8cc5911e528d0555ee89fe63f0e30b8a3eac4a32e3e4237ee9b00a38107a7d1b"
RHO = Fraction(743, 1125)
COEFFICIENTS = (
    (Fraction(34, 15), Fraction(1261, 225)),
    (Fraction(61, 30), Fraction(2329, 450)),
    (Fraction(31, 15), Fraction(1189, 225)),
    (Fraction(32, 15), Fraction(1223, 225)),
)


def require(condition, label):
    if not condition:
        raise ArithmeticError(label)


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def snapshot(packet):
    return {p.name: digest(p) for p in sorted(packet.iterdir()) if p.is_file()}


@lru_cache(maxsize=None)
def primitive_from_denominators(a, b):
    """Use reduced coordinate denominators, not the author's gcd algorithm."""
    x = Fraction(1, 20) + Fraction(1, 10 * (1 << a))
    z = Fraction(1, 20) + Fraction(1, 10 * (1 << b))
    y = 1 - x - z
    total = lcm(x.denominator, y.denominator, z.denominator)
    triple = tuple(q.numerator * (total // q.denominator) for q in (x, y, z))
    require(min(triple) > 0 and sum(triple) == total, ("positive shape", a, b))
    require(gcd(gcd(triple[0], triple[1]), triple[2]) == 1, ("primitive shape", a, b))
    return total, triple


def classified_scale(a, b):
    m = max(a, b)
    if m == 0:
        return 20
    if m == 1:
        return 10 if a == b else 20
    return (1 << (m + 1)) if a % 4 == b % 4 == 3 else 10 * (1 << m)


def decode_endpoint(g, total):
    denominator = 20 * g - total
    if denominator <= 0:
        return None
    power, remainder = divmod(2 * total, denominator)
    if remainder or power <= 0 or power & (power - 1):
        return None
    return power.bit_length() - 1


def floor_sum(n, base):
    power, k, answer = 1, 0, 0
    while power <= n:
        answer += (2 * k + 1) * (n // power)
        power *= base
        k += 1
    return answer


def digit_sum_formula(n, base):
    original, s, w, j = n, 0, 0, 0
    while n:
        n, digit = divmod(n, base)
        s += digit
        w += j * digit
        j += 1
    numerator = base * (base + 1) * original - (3 * base - 1) * s - 2 * (base - 1) * w
    answer, remainder = divmod(numerator, (base - 1) ** 2)
    require(remainder == 0, ("digit identity integrality", original, base))
    return answer


def count_by_floor_formula(n):
    return floor_sum(n // 10, 2) + floor_sum(n // 16, 16) - floor_sum(n // 80, 16)


def shell_formula(n):
    valuation = (n & -n).bit_length() - 1
    return valuation ** 2 if n % 5 == 0 else (valuation // 4) ** 2


def direct_count(n):
    # d >= 2^(max(a,b)+1): this inclusive square is a safe finite superset.
    bound = n.bit_length() - 1
    return sum(n // primitive_from_denominators(a, b)[0]
               for a in range(bound + 1) for b in range(bound + 1))


def inverse_by_binary_search(rank):
    low, high = 0, 10 * rank
    while low < high:
        middle = (low + high) // 2
        if count_by_floor_formula(middle) >= rank:
            high = middle
        else:
            low = middle + 1
    return low


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("packet", type=Path)
    parser.add_argument("--dependency", type=Path, default=None,
                        help="Optional path to the frozen primitive-input PROOF.md")
    args = parser.parse_args()
    packet = args.packet.resolve()
    dependency = args.dependency or packet.parent / "native-gap-halting-continuation-20261004" / "PROOF.md"
    before = snapshot(packet)
    require(before["PROOF.md"] == PROOF_SHA, "counting proof hash")
    require(before["MANIFEST.json"] == MANIFEST_SHA, "counting manifest hash")
    require(digest(dependency) == DEPENDENCY_SHA, "primitive dependency hash")
    manifest = json.loads((packet / "MANIFEST.json").read_text())
    for entry in manifest["files"]:
        path = packet / entry["path"]
        require(path.resolve().parent == packet, "manifest path remains in packet")
        require(path.stat().st_size == entry["bytes"], ("manifest byte count", entry["path"]))
        require(digest(path) == entry["sha256"], ("manifest hash", entry["path"]))

    grid_max, ceiling, brute_max, digital_max = 64, 250000, 160, 2048
    shapes = set()
    partial_reciprocal = Fraction(0)
    for a in range(grid_max + 1):
        for b in range(grid_max + 1):
            scale, triple = primitive_from_denominators(a, b)
            require(scale == classified_scale(a, b), ("scale classification", a, b))
            require(scale >= 1 << (max(a, b) + 1), ("scale lower bound", a, b))
            require(triple not in shapes, ("distinct shapes", a, b))
            shapes.add(triple)
            require(decode_endpoint(triple[0], scale) == a, ("decode a", a, b))
            require(decode_endpoint(triple[2], scale) == b, ("decode b", a, b))
            partial_reciprocal += Fraction(1, scale)
    tail_bound = Fraction(2 * grid_max + 5, 1 << (grid_max + 1))
    require(0 < RHO - partial_reciprocal <= tail_bound, "reciprocal partial sum and rigorous tail bound")

    primitive_multiplicity = Counter()
    bound = ceiling.bit_length() - 1
    for a in range(bound + 1):
        for b in range(bound + 1):
            scale = primitive_from_denominators(a, b)[0]
            if scale <= ceiling:
                primitive_multiplicity[scale] += 1
    shells = [0] * (ceiling + 1)
    for scale, multiplicity in primitive_multiplicity.items():
        for n in range(scale, ceiling + 1, scale):
            shells[n] += multiplicity

    # Independent exhaustive positive-triple test, using only the exact decoder.
    brute_shells = [0] * (brute_max + 1)
    examined_triples = 0
    for total in range(1, brute_max + 1):
        for g1 in range(1, total - 1):
            a = decode_endpoint(g1, total)
            for g3 in range(1, total - g1):
                examined_triples += 1
                b = decode_endpoint(g3, total)
                if a is not None and b is not None:
                    scale, triple = primitive_from_denominators(a, b)
                    require(total % scale == 0, ("integer primitive multiple", total, g1, g3))
                    multiplier = total // scale
                    require(tuple(multiplier * x for x in triple) == (g1, total - g1 - g3, g3),
                            ("unique primitive multiple", total, g1, g3))
                    brute_shells[total] += 1
        require(brute_shells[total] == shells[total], ("exhaustive positive triples", total))

    cumulative = distinct = inverse_ranks = 0
    for n in range(1, ceiling + 1):
        require(shells[n] == shell_formula(n), ("shell", n))
        previous = cumulative
        cumulative += shells[n]
        require(cumulative == count_by_floor_formula(n), ("cumulative floor count", n))
        distinct += int(shells[n] > 0)
        require(distinct == n // 10 + n // 16 - n // 80, ("distinct count", n))
        ell = n.bit_length() - 1
        error_numerator = 743 * n - 1125 * cumulative
        require(0 <= error_numerator < 1125 * (ell * ell + 4 * ell + 6), ("global error", n))
        if shells[n]:
            # These inequalities verify every rank in the entire tied block.
            for rank in range(previous + 1, cumulative + 1):
                require(743 * n - 1125 * rank >= 0, ("inverse nonnegative deviation", rank))
                require(previous < rank <= cumulative, ("inverse block membership", rank))
                require(n <= 10 * rank, ("inverse upper bound", rank))
                inverse_ranks += 1

    digital_checks = 0
    for base in range(2, 33):
        for n in range(digital_max + 1):
            require(floor_sum(n, base) == digit_sum_formula(n, base), ("floor/digit identity", base, n))
            digital_checks += 1
    require(count_by_floor_formula(0) == 0 and floor_sum(0, 2) == 0, "zero input endpoints")
    require([count_by_floor_formula(n) for n in (9, 10, 15, 16, 19, 20, 40)]
            == [0, 1, 1, 2, 2, 6, 17], "small count endpoints")
    require([inverse_by_binary_search(n) for n in range(1, 7)] == [10, 16, 20, 20, 20, 20],
            "small inverse endpoints")

    subsequence_max, direct_max = 400, 48
    extra_small_nondividing_pairs = 0
    for m in range(1, subsequence_max + 1):
        total = 10 * (1 << m)
        current, previous = count_by_floor_formula(total), count_by_floor_formula(total - 1)
        alpha, beta = COEFFICIENTS[m % 4]
        e = RHO * total - current
        require(e == alpha * m + beta, ("residue-class error", m))
        require(current - previous == (m + 1) ** 2, ("square jump", m))
        require(RHO * (total - 1) - previous == e + (m + 1) ** 2 - RHO,
                ("left-neighbor error", m))
        first, last = previous + 1, current
        require(Fraction(total) - first / RHO == (m * m + (2 + alpha) * m + beta) / RHO,
                ("first-rank exact deviation", m))
        require(Fraction(total) - last / RHO == (alpha * m + beta) / RHO,
                ("last-rank exact deviation", m))
        require(previous < first <= current and previous < last <= current, ("endpoint rank membership", m))
        if m <= direct_max:
            require(direct_count(total) == current and direct_count(total - 1) == previous,
                    ("denominator-derived subsequence counts", m))
            require(inverse_by_binary_search(first) == total and inverse_by_binary_search(last) == total,
                    ("binary-search inverse endpoints", m))
            for a in range(m + 4):
                for b in range(m + 4):
                    maximum = max(a, b)
                    scale = primitive_from_denominators(a, b)[0]
                    require((total % scale == 0) == (maximum <= m), ("divisibility cutoff", m, a, b))
                    if maximum > m and scale <= total:
                        require(total % scale != 0 and maximum - m in (1, 2)
                                and a % 4 == b % 4 == 3, ("size versus divisibility", m, a, b))
                        extra_small_nondividing_pairs += 1
    require(primitive_from_denominators(3, 3)[0] == 16 < 20 and 20 % 16 != 0,
            "explicit strict-size counterexample to an incorrect cutoff")

    # Independent rational evaluation of the limiting mean shell multiplicity.
    half, sixteenth = Fraction(1, 2), Fraction(1, 16)
    sum_v_squared = half * (1 + half) / (1 - half) ** 3 / 2
    sum_group_squared = sixteenth * (1 + sixteenth) / (1 - sixteenth) ** 3
    shell_mean = sum_v_squared / 5 + Fraction(3, 4) * sum_group_squared
    require(shell_mean == RHO, "independent shell-mean constant")
    require(Fraction(1, 10) + Fraction(1, 16) - Fraction(1, 80) == Fraction(3, 20), "distinct density")
    require(snapshot(packet) == before, "source packet unchanged")
    require(digest(dependency) == DEPENDENCY_SHA, "primitive dependency unchanged")
    result = {
        "status": "PASS",
        "checker_sha256": digest(Path(__file__)),
        "source_hashes_verified_unchanged": before,
        "primitive_dependency_sha256_verified_unchanged": DEPENDENCY_SHA,
        "method": "Independent reduced-coordinate-denominator/lcm primitives, exhaustive positive triples, exact integer and rational arithmetic; no packet code execution",
        "counter_grid_inclusive": [0, grid_max],
        "primitive_shapes_checked": len(shapes),
        "exhaustive_positive_triples_max_total": brute_max,
        "positive_triples_examined": examined_triples,
        "all_total_scales_checked_inclusive": [1, ceiling],
        "A_at_ceiling": cumulative,
        "B_at_ceiling": distinct,
        "inverse_ranks_checked_in_shell_blocks": inverse_ranks,
        "digit_identity_bases_inclusive": [2, 32],
        "digit_identity_arguments_inclusive": [0, digital_max],
        "digit_identity_checks": digital_checks,
        "exact_residue_and_inverse_endpoint_M_inclusive": [1, subsequence_max],
        "independent_lcm_count_and_binary_inverse_M_inclusive": [1, direct_max],
        "small_but_nondividing_special_pairs_seen": extra_small_nondividing_pairs,
        "rho": str(RHO),
        "distinct_scale_density": "3/20",
        "inverse_slope_and_sharp_limsup": str(1 / RHO),
        "scope_limit": "Finite evidence, not a proof of limiting assertions; mathematical proofs are in REVIEW.md. Encoded initializations only, not halting inputs, witness tuples, or an OEIS open-problem result."
    }
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
