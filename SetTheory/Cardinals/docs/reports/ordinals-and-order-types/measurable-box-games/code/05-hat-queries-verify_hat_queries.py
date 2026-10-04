#!/usr/bin/env python3
"""Exact finite audit of the paired rare-loss hat strategy.

The mathematical block rule is from Nathaniel Eldredge,
"A probabilistic look at the infinite hat-guessing game",
arXiv:2508.02828v2, Proposition 6.6.  This program audits a partner-first,
short-circuit implementation and its query-cost distribution.

Within a block, zero-based players are S_0,D_0,S_1,D_1,... . Hats are
0 (black) or 1 (white). Each D-player guesses opposite to its partner.
An S-player first queries its partner. A white partner causes an immediate
guess of 1. Otherwise it scans the remaining visible hats, stopping at the
first white hat and guessing 0; if there is none, it guesses 1.

Run with Python 3.10 or later; no third-party packages are required:

    python verify_hat_queries.py

The default exhaustive range is 1 through 8 pairs. The deterministic JSON
report is written next to this program unless --output specifies a path.
All equalities and probabilities are checked with integers or Fractions.
These are finite executable checks, not proof-assistant certificates or
proofs of any infinite almost-sure or asymptotic assertion.
"""

from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
import json
from pathlib import Path


class VerificationError(RuntimeError):
    """Raised by a failed check, including when Python runs with -O."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise VerificationError(message)


def run_player(
    hats: int, player: int, pair_count: int
) -> tuple[int, tuple[tuple[int, int], ...]]:
    """Run the legal query algorithm and return its guess and transcript.

The only access to a hat's value occurs inside query(). Its guards reject
the player's own coordinate, out-of-range coordinates, and repeat queries.
"""
    size = 2 * pair_count
    transcript: list[tuple[int, int]] = []
    seen: set[int] = set()

    def query(index: int) -> int:
        require(0 <= index < size, "Out-of-range query")
        require(index != player, "Own-hat query")
        require(index not in seen, "Repeated query")
        seen.add(index)
        answer = (hats >> index) & 1
        transcript.append((index, answer))
        return answer

    partner = player ^ 1
    partner_hat = query(partner)
    if player % 2:
        return 1 - partner_hat, tuple(transcript)
    if partner_hat:
        return 1, tuple(transcript)
    for index in range(size):
        if index == player or index == partner:
            continue
        if query(index):
            return 0, tuple(transcript)
    return 1, tuple(transcript)


def declarative_guess(hats: int, player: int, pair_count: int) -> int:
    """Independent closed-form version of the mathematical guessing rule."""
    partner = player ^ 1
    partner_hat = (hats >> partner) & 1
    if player % 2:
        return 1 - partner_hat
    outside_pair_mask = ((1 << (2 * pair_count)) - 1) ^ (
        (1 << player) | (1 << partner)
    )
    return int(bool(partner_hat) or (hats & outside_pair_mask) == 0)


def expected_block_surplus(hats: int, pair_count: int) -> int:
    """The three-case score law, without executing any predictions."""
    if hats == 0:
        return -pair_count
    if hats.bit_count() == 1:
        white_index = hats.bit_length() - 1
        if white_index % 2 == 0:
            return 1
    return 0


def rational_text(value: Fraction) -> str:
    """Stable exact JSON representation of a rational number."""
    return str(value)


def verify_block(pair_count: int) -> dict:
    size = 2 * pair_count
    assignments = 1 << size
    maximum_queries = size - 1
    query_histograms: list[Counter[int]] = [Counter() for _ in range(size)]
    correct_counts = [0] * size
    score_counts: Counter[int] = Counter()
    total_primary_queries = 0

    for hats in range(assignments):
        twice_surplus = 0
        prefixes = [0]
        for player in range(size):
            guess, transcript = run_player(hats, player, pair_count)
            require(
                guess == declarative_guess(hats, player, pair_count),
                f"Operational/declarative mismatch: m={pair_count}, "
                f"hats={hats}, player={player}",
            )
            own_flip = run_player(hats ^ (1 << player), player, pair_count)
            require(
                own_flip == (guess, transcript),
                f"Own-hat change affects execution: m={pair_count}, "
                f"hats={hats}, player={player}",
            )
            query_count = len(transcript)
            require(1 <= query_count <= maximum_queries, "Wrong query bound")
            query_histograms[player][query_count] += 1
            total_primary_queries += query_count
            correct = int(guess == ((hats >> player) & 1))
            correct_counts[player] += correct
            twice_surplus += 2 * correct - 1
            prefixes.append(twice_surplus)

        require(twice_surplus % 2 == 0, "Nonintegral complete-block surplus")
        surplus = twice_surplus // 2
        expected = expected_block_surplus(hats, pair_count)
        require(surplus == expected, f"Wrong score law for m={pair_count}")
        score_counts[surplus] += 1

        if hats == 0:
            require(
                prefixes == [-length for length in range(size + 1)],
                "Not every player loses in the all-black block",
            )
        else:
            require(
                all(prefixes[2 * j] <= prefixes[2 * j + 2]
                    for j in range(pair_count)),
                "A nonbad block decreases at a completed-pair boundary",
            )
            if surplus == 1:
                require(
                    all(-2 <= value - twice_surplus <= 1 for value in prefixes),
                    "Success-block endpoint error leaves [-1, 1/2]",
                )
            else:
                require(
                    all(abs(value - twice_surplus) <= 1 for value in prefixes),
                    "Zero-surplus block endpoint error exceeds 1/2",
                )
            require(
                all(abs(value - twice_surplus) <= 2 for value in prefixes),
                "Good-block endpoint error exceeds 1",
            )

    expected_counts = {
        -pair_count: 1,
        0: assignments - pair_count - 1,
        1: pair_count,
    }
    require(dict(score_counts) == expected_counts, "Wrong aggregate score law")
    require(
        sum(score * count for score, count in score_counts.items()) == 0,
        "Finite score does not have mean zero",
    )
    require(
        all(count * 2 == assignments for count in correct_counts),
        "A player's probability of success differs from 1/2",
    )

    expected_s_cost = Fraction(2) - Fraction(1, 1 << (size - 2))
    s_histogram: Counter[int] = Counter()
    for query_count in range(1, maximum_queries):
        s_histogram[query_count] = assignments >> query_count
    s_histogram[maximum_queries] = assignments >> (maximum_queries - 1)
    expected_tails = []
    for threshold in range(maximum_queries + 2):
        probability = (
            Fraction(1, 1 << threshold)
            if threshold < maximum_queries
            else Fraction(0)
        )
        expected_tails.append({
            "integer_threshold": threshold,
            "P_Q_S_gt_threshold": rational_text(probability),
        })

    for player, histogram in enumerate(query_histograms):
        if player % 2:
            require(histogram == Counter({1: assignments}), "D cost is not 1")
            continue
        require(histogram == s_histogram, "Wrong full S query-cost distribution")
        average = Fraction(
            sum(cost * count for cost, count in histogram.items()), assignments
        )
        require(average == expected_s_cost, "Wrong exact expected S cost")
        for tail in expected_tails:
            threshold = tail["integer_threshold"]
            actual = Fraction(
                sum(count for cost, count in histogram.items() if cost > threshold),
                assignments,
            )
            require(
                rational_text(actual) == tail["P_Q_S_gt_threshold"],
                "Wrong S query-cost tail",
            )

    expected_pair_average = (expected_s_cost + 1) / 2
    require(
        Fraction(total_primary_queries, size * assignments) == expected_pair_average,
        "Wrong average query count over physical players",
    )
    return {
        "pair_count": pair_count,
        "physical_players": size,
        "physical_hat_assignments": assignments,
        "primary_player_executions": assignments * size,
        "own_hat_flip_reexecutions": assignments * size,
        "primary_queries_executed": total_primary_queries,
        "score_counts": {str(score): count for score, count in sorted(score_counts.items())},
        "score_probabilities": {
            str(score): rational_text(Fraction(count, assignments))
            for score, count in sorted(score_counts.items())
        },
        "expected_S_query_count": rational_text(expected_s_cost),
        "expected_D_query_count": "1",
        "expected_query_count_per_physical_player": rational_text(expected_pair_average),
        "maximum_queries": maximum_queries,
        "S_query_count_histogram": {
            str(cost): count for cost, count in sorted(s_histogram.items())
        },
        "S_query_tail": expected_tails,
        "checks": {
            "only_visible_distinct_hats_queried": "passed",
            "same_guess_and_transcript_after_own_hat_flip": "passed",
            "operational_rule_matches_declarative_rule": "passed",
            "pointwise_three_case_block_score": "passed",
            "exact_aggregate_score_distribution": "passed",
            "every_player_is_individually_fair": "passed",
            "all_black_block_every_guess_wrong": "passed",
            "good_block_even_prefix_monotonicity": "passed",
            "success_block_endpoint_error_in_minus1_to_half": "passed",
            "zero_block_endpoint_error_at_most_half": "passed",
            "exact_query_distribution_expectation_and_tail": "passed",
        },
    }


def verify_stage_accounting() -> list[dict]:
    """Exact finite accounting for epsilon=1; no asymptotic claim is tested."""
    physical_players = 0
    expected_successes = Fraction(0)
    expected_bad_blocks = Fraction(0)
    selected_stages = {2, 4, 8, 12, 20, 40, 80}
    records = []
    for stage in range(2, 81):
        fourth_power = 4 ** stage
        repetitions = (fourth_power + stage * stage - 1) // (stage * stage)
        require(repetitions * stage * stage >= fourth_power, "Ceiling too small")
        require((repetitions - 1) * stage * stage < fourth_power, "Ceiling too large")
        physical_players += 2 * stage * repetitions
        expected_successes += Fraction(stage * repetitions, fourth_power)
        expected_bad_blocks += Fraction(repetitions, fourth_power)
        if stage in selected_stages:
            records.append({
                "last_stage": stage,
                "stage_block_repetitions": repetitions,
                "cumulative_physical_players": physical_players,
                "cumulative_expected_success_blocks": rational_text(expected_successes),
                "cumulative_expected_bad_blocks": rational_text(expected_bad_blocks),
                "ratio_N_M_to_8_over_3_times_4powM_over_M": rational_text(
                    Fraction(3 * physical_players * stage, 8 * fourth_power)
                ),
            })
    return records


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-pairs", type=int, default=8)
    parser.add_argument(
        "--output", type=Path,
        default=Path(__file__).with_name("hat_query_verification.json"),
    )
    args = parser.parse_args()
    if args.max_pairs < 1:
        parser.error("--max-pairs must be at least 1")
    blocks = []
    for pair_count in range(1, args.max_pairs + 1):
        record = verify_block(pair_count)
        blocks.append(record)
        print(
            f"m={pair_count}: {record['physical_hat_assignments']:,} assignments; "
            f"E[Q_S]={record['expected_S_query_count']}; all checks passed",
            flush=True,
        )
    report = {
        "status": "passed",
        "source": {
            "author": "Nathaniel Eldredge",
            "title": "A probabilistic look at the infinite hat-guessing game",
            "version": "arXiv:2508.02828v2",
            "url": "https://arxiv.org/html/2508.02828v2",
            "mathematical_block_rule": "Proposition 6.6",
            "implementation": "partner-first short-circuit visible-hat search",
        },
        "arithmetic": "exact integers and fractions.Fraction",
        "scope": "finite exhaustive physical-hat checks and finite stage accounting",
        "not_verified_by_this_program": [
            "the infinite almost-sure divergence theorem",
            "the infinite asymptotic growth theorem",
            "the Boolean hypercontractivity obstruction",
            "historical priority",
            "proof-assistant kernel correctness",
        ],
        "totals": {
            "minimum_pairs": 1,
            "maximum_pairs": args.max_pairs,
            "physical_hat_assignments": sum(b["physical_hat_assignments"] for b in blocks),
            "primary_player_executions": sum(b["primary_player_executions"] for b in blocks),
            "own_hat_flip_reexecutions": sum(b["own_hat_flip_reexecutions"] for b in blocks),
            "primary_queries_executed": sum(b["primary_queries_executed"] for b in blocks),
        },
        "blocks": blocks,
        "epsilon_one_finite_stage_accounting": verify_stage_accounting(),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"Wrote {args.output}")


if __name__ == "__main__":
    main()
