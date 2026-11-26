#!/usr/bin/env python3
"""Exact certificates for the second-moment spanning refinement.

Only the Python standard library is used.  Fractions are authoritative;
decimal approximations are printed solely to make the output readable.

The mathematical hypotheses are the two separate bounds
  dim U - u*dim S <= ||PB pr_U||_HS^2,
  d * mean_g ||B* rho(g) B||_HS^2 <= (1+v)*s^2.
For s>0, 0<=u<1, v>=0, the paper proves the preimage profile
  dim A_g^{-1}(F) <= s*u + s*sqrt((1+v)*dim F/d).
This program certifies the integer greedy consequences of that profile.
It does not verify the arithmetic hypotheses for a new Galois representation
and is not a Lean or kernel verification.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction as Q
from pathlib import Path


def ceil_q(x: Q) -> int:
    return -((-x.numerator) // x.denominator)


def encode_q(x: Q) -> dict:
    return {
        "numerator": x.numerator,
        "denominator": x.denominator,
        "decimal_illustration": float(x),
    }


def below_profile(j: int, k: int, d: int, s: int, u: Q, v: Q) -> bool:
    """Exact comparison j <= s*u+s*sqrt((1+v)*k/d), without roots."""
    excess = Q(j) - s * u
    return excess <= 0 or excess * excess <= s * s * (1 + v) * k / d


def capped_floor_profile(k: int, d: int, s: int, u: Q, v: Q) -> int:
    lo, hi = 0, s
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if below_profile(mid, k, d, s, u, v):
            lo = mid
        else:
            hi = mid - 1
    # These two comparisons independently certify the binary-search result.
    assert below_profile(lo, k, d, s, u, v)
    assert lo == s or not below_profile(lo + 1, k, d, s, u, v)
    return lo


def greedy_certificate(d: int, s: int, u: Q, v: Q) -> dict:
    assert d > 0 and s > 0 and 0 <= u < 1 and v >= 0
    # Necessary for any instance: rank(PB) >= (1-u)*s and rank(PB) <= d.
    assert (1 - u) * s <= d
    alpha = (1 - u) ** 2 / (1 + v)
    threshold = alpha * d
    R = ceil_q(threshold)
    floor_profile = [capped_floor_profile(k, d, s, u, v) for k in range(R + 1)]
    transitions = [min(R, k + s - floor_profile[k]) for k in range(R + 1)]
    # Taking a suffix minimum is essential: an actual current rank may exceed
    # its certified lower bound, and the raw transition need not be monotone.
    envelope = transitions[:]
    for k in range(R - 1, -1, -1):
        envelope[k] = min(transitions[k], envelope[k + 1])
    for k in range(R):
        assert transitions[k] >= k + 1
        assert envelope[k] >= k + 1
        assert envelope[k] == min(transitions[k], envelope[k + 1])
    assert envelope[R] == R
    ranks = [0]
    while ranks[-1] < R:
        ranks.append(envelope[ranks[-1]])
    assert len(ranks) - 1 <= R
    assert all(x < y for x, y in zip(ranks, ranks[1:]))
    return {
        "d": d,
        "s": s,
        "near_isometry_error": encode_q(u),
        "moment_excess": encode_q(v),
        "universal_rank_fraction": encode_q(alpha),
        "unrounded_rank_lower_bound": encode_q(threshold),
        "integer_rank_target": R,
        "independent_kernel_rank_lower_bound": ceil_q((1 - u) * s),
        "translates_to_target": len(ranks) - 1,
        "rank_lower_bounds": ranks,
        "verified_transition_states": R + 1,
        "scope": "Strongest monotone rank guarantee from this one-step profile; not a proof of optimal translate count among all actual unitary instances.",
    }


def log_unit_interval(x: Q, terms: int) -> tuple[Q, Q]:
    """Rigorous rational bounds for log(x), 1 <= x <= 2."""
    assert 1 <= x <= 2
    z = (x - 1) / (x + 1)
    total = Q(0)
    power = z
    for j in range(terms):
        total += 2 * power / (2 * j + 1)
        power *= z * z
    tail = 2 * power / ((2 * terms + 1) * (1 - z * z))
    return total, total + tail


def log_interval_integer(x: int, terms: int = 24) -> tuple[Q, Q]:
    """Range reduction keeps every atanh-series argument at most 1/3."""
    assert x >= 1
    k = x.bit_length() - 1
    y = Q(x, 2 ** k)
    lo2, hi2 = log_unit_interval(Q(2), terms)
    loy, hiy = log_unit_interval(y, terms)
    return k * lo2 + loy, k * hi2 + hiy


def certified_budget_floor(B: int, d: int, s: int, multiplier: int) -> tuple[int, int]:
    """Certify floor((multiplier*d/s) log(1+2B^2)) by rational bounds."""
    terms = 12
    while True:
        lo, hi = log_interval_integer(1 + 2 * B * B, terms)
        low_floor = (multiplier * d * lo / s).__floor__()
        high_floor = (multiplier * d * hi / s).__floor__()
        if low_floor == high_floor:
            return low_floor, terms
        terms *= 2
        assert terms <= 1536


def first_at_least(ranks: list[int], target: int) -> int | None:
    return next((j for j, r in enumerate(ranks) if r >= target), None)


def cyclic_equality_model(a: int, b: int, copies: int = 1) -> dict:
    """Enumerate a concrete cyclic permutation action and all Gram overlaps.

    epsilon=a/b; each copy has b(b+a) coordinates, of which (b-a)^2
    are cyclically permuted.  The rest are fixed.  Each source basis vector
    maps to sqrt(1-epsilon) times the first active coordinate in its copy.
    All computations only need the rational squared scale.
    """
    assert 0 <= a < b and copies > 0
    epsilon = Q(a, b)
    block_dimension = b * (b + a)
    active = (b - a) ** 2
    d, s = copies * block_dimension, copies
    source_positions = [j * block_dimension for j in range(copies)]
    squared_scale = 1 - epsilon
    orbit_positions = set()
    overlap_squares = []
    for g in range(active):
        permutation = list(range(d))
        for block in range(copies):
            offset = block * block_dimension
            for i in range(active):
                permutation[offset + i] = offset + (i + g) % active
        assert sorted(permutation) == list(range(d))
        moved = [permutation[x] for x in source_positions]
        orbit_positions.update(moved)
        # Entry (i,j) is squared_scale if the j-th image hits source i, else0.
        nonzero_entries = sum(x == y for x in source_positions for y in moved)
        overlap_squares.append(nonzero_entries * squared_scale ** 2)
    mean_overlap = sum(overlap_squares, Q(0)) / active
    alpha = (1 - epsilon) ** 2 / (1 + epsilon)
    assert d * mean_overlap == (1 + epsilon) * s * s
    assert Q(len(orbit_positions), d) == alpha
    # A*A=(1-epsilon)I implies the near-isometry condition on every subspace:
    # (1-epsilon)dimU >= dimU-epsilon*s, since dimU<=s.
    for dim_u in range(s + 1):
        assert squared_scale * dim_u >= dim_u - epsilon * s
    return {
        "epsilon": encode_q(epsilon),
        "source_dimension": s,
        "target_dimension": d,
        "group_order": active,
        "orbit_span_dimension": len(orbit_positions),
        "mean_squared_HS_overlap": encode_q(mean_overlap),
        "moment_bound_is_equality": True,
        "universal_rank_bound_is_equality": True,
        "unitarity_certificate": "Every enumerated action matrix is a permutation matrix.",
    }


def source_specialization(B: int, d: int = 1000, s: int = 20, multiplier: int = 4) -> dict:
    assert (multiplier == 4 and B >= 6) or (multiplier == 5 and B >= 4)
    u, v = Q(5, B ** 4), Q(9, B ** 4)
    cert = greedy_certificate(d, s, u, v)
    budget, terms = certified_budget_floor(B, d, s, multiplier)
    original_budget, _ = certified_budget_floor(B, d, s, 5)
    ranks = cert["rank_lower_bounds"]
    before_restriction = ranks[min(budget, len(ranks) - 1)]
    # The source gives codim(U) <= s/B^8; codimension is an integer.
    restriction_codimension = (Q(s, B ** 8)).__floor__()
    candidates = [
        (r - j * restriction_codimension, j)
        for j, r in enumerate(ranks)
        if j <= budget
    ]
    best_rank, best_steps = max(candidates, key=lambda t: (t[0], -t[1]))
    old_target = ceil_q((1 - Q(4, B * B)) * d)
    new_target = ceil_q((1 - Q(20, B ** 4)) * d)
    alpha = (1 - u) ** 2 / (1 + v)
    delta = 1 - alpha
    h_upper = (1 + v) / (2 * (1 - u) ** 2)
    assert h_upper <= Q(33920, 63001) < 1
    assert delta <= Q(19, B ** 4)
    if multiplier == 4:
        # Rate exponent >=2, e^h<3, and (1+2B^2)^2 >=4B^4.
        simple_deficit_bound = Q(19, B ** 4) + Q(3, 4 * B ** 4) + Q(8, B ** 6)
    else:
        # Same five-times budget as upstream: exponent >=5/2.
        simple_deficit_bound = Q(19, B ** 4) + Q(1, B ** 5) + Q(10, B ** 6)
    assert simple_deficit_bound < Q(20, B ** 4)
    cert["source_specialization"] = {
        "B": B,
        "budget_multiplier": multiplier,
        "integer_translate_budget": budget,
        "original_five_times_integer_budget": original_budget,
        "log_series_terms_used_to_certify_floor": terms,
        "old_stated_integer_rank_target": old_target,
        "new_proved_integer_rank_target": new_target,
        "translates_to_old_target_before_restriction": first_at_least(ranks, old_target),
        "translates_to_new_target_before_restriction": first_at_least(ranks, new_target),
        "full_source_rank_at_budget": before_restriction,
        "integer_upper_bound_for_source_codimension": restriction_codimension,
        "best_certified_restricted_rank_at_budget": best_rank,
        "steps_used_for_that_rank": best_steps,
        "rate_upper_bound": encode_q(h_upper),
        "limiting_deficit": encode_q(delta),
        "simple_analytic_deficit_bound": encode_q(simple_deficit_bound),
        "interpretation": "Illustrative dimension parameters with the source's error formulas; not an arithmetic realization of those dimensions.",
    }
    return cert


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="Write complete JSON to this path.")
    args = parser.parse_args()
    common = greedy_certificate(1000, 20, Q(1, 100), Q(1, 100))
    common["translates_to_rank_840"] = first_at_least(common["rank_lower_bounds"], 840)
    assert common["translates_to_rank_840"] == 148
    assert common["integer_rank_target"] == 971
    assert common["translates_to_target"] == 261
    # Exact algebra behind the all-B>=4 estimates:
    # 19q(1+9q) - (19q-25q^2) = 196q^2 >=0;
    # 3/(2^(5/2)) <1 because9<32;
    # 1/B+10/B^2 <=1/4+10/16=7/8 <1.
    assert 19 * 9 + 25 == 196
    assert 9 < 32
    assert Q(1, 4) + Q(10, 16) == Q(7, 8)
    assert 19 + Q(3, 4) + Q(8, 36) < 20
    result = {
        "status": "PASS",
        "arithmetic": "Python fractions.Fraction and exact integer comparisons",
        "claims_checked": [
            "Exact square-root-free floor certificates for every greedy state",
            "Suffix-envelope recurrence and its finite termination",
            "Explicit cyclic permutation equality examples",
            "Rational source-error algebra and certified logarithmic budget floors",
        ],
        "important_scope": "The universal rank fraction is sharp. Fixed-dimension optimum and optimal translate count are not claimed. The analytic and arithmetic hypotheses are proved in the manuscript or supplied by the pinned upstream declarations; this script is not a replacement for those proofs.",
        "equality_examples": [cyclic_equality_model(0, 2), cyclic_equality_model(1, 3, 2), cyclic_equality_model(2, 5)],
        "common_error_example": common,
        "source_error_examples": [source_specialization(4, multiplier=5)] +
            [source_specialization(B) for B in (6, 10, 100)],
    }
    rendered = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered)
        print(json.dumps({"status": result["status"], "output": str(args.output), "examples": 8}))
    else:
        print(rendered, end="")


if __name__ == "__main__":
    main()
