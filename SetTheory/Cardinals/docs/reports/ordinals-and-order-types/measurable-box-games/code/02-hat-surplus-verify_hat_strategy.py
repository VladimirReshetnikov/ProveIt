#!/usr/bin/env python3
"""Exhaustive finite checks for the interleaved binary hat-guessing gadget.

This program is original code written for the accompanying research article.
It uses only the Python standard library.  See LICENSE.txt for the license.

The program verifies finite instances, not the article's infinite theorem.
In particular, enumerating all inputs below is not a formal proof of any
statement quantified over all r, a, or all infinite hat sequences.

Conventions
-----------
* r >= 1, t = 2**r - 1, a >= 1, and N = 2*a*t.
* Player order is (round, column, mate), with round = 0,...,a-1,
  column = 1,...,t, and mate = 0,1.
* Column labels are the nonzero vectors of F_2**r, encoded as integers.
  Vector addition is bitwise XOR.
* Bit i of ``word`` is the hat of player i.  Displayed hat strings are in
  player order, so their leftmost character is bit 0 (not the usual order
  of a displayed binary integer).
* C_u is the number of correct guesses among the first u players, and
  D_u = C_u - u/2.  The prefix reference on a good input is u/(2*t).

Two prediction implementations are cross-checked on every input:

1. ``group_prediction`` uses parity of the entire repeated-column groups.
2. ``visible_pair_prediction`` independently reads only other mate-pairs
   and the player's mate.  It never reads the player's own hat.

Both implementations are also evaluated after toggling the player's own
hat.  All comparisons and bound checks use exact integer arithmetic.

Example invocation from this file's directory:

    python verify_hat_strategy.py

The default output is ../data/verification.json; two small example files
are written beside it.  Use --case R A repeatedly to change the cases.
"""

from __future__ import annotations

import argparse
import csv
import json
import platform
import sys
import time
from collections import Counter
from dataclasses import dataclass
from datetime import datetime, timezone
from fractions import Fraction
from pathlib import Path
from typing import Any


DEFAULT_CASES = (
    (1, 1), (1, 2), (1, 3), (1, 4), (1, 5),
    (2, 1), (2, 2), (2, 3),
    (3, 1),
)


class VerificationFailure(RuntimeError):
    """A failed verification, with enough information to reproduce it."""


@dataclass(frozen=True)
class Gadget:
    r: int
    a: int
    t: int
    n: int
    pair_columns: tuple[int, ...]
    group_masks: tuple[int, ...]

    @classmethod
    def create(cls, r: int, a: int) -> "Gadget":
        if r < 1 or a < 1:
            raise ValueError("r and a must both be positive integers")
        t = (1 << r) - 1
        n = 2 * a * t
        pair_columns = tuple(1 + pair % t for pair in range(a * t))
        masks = [0] * t
        for pair, column in enumerate(pair_columns):
            masks[column - 1] |= 3 << (2 * pair)
        return cls(r, a, t, n, pair_columns, tuple(masks))

    def coordinates(self, position: int) -> tuple[int, int, int]:
        pair, mate = divmod(position, 2)
        round_number, zero_based_column = divmod(pair, self.t)
        return round_number, zero_based_column + 1, mate


def group_state(word: int, gadget: Gadget) -> tuple[tuple[int, ...], int]:
    """Compute all whole-group parities and their full syndrome."""
    parities = tuple((word & mask).bit_count() & 1
                     for mask in gadget.group_masks)
    syndrome = 0
    for column, parity in enumerate(parities, start=1):
        if parity:
            syndrome ^= column
    return parities, syndrome


def group_prediction(
    word: int,
    position: int,
    gadget: Gadget,
    state: tuple[tuple[int, ...], int] | None = None,
) -> int:
    """Whole-group formulation of the strategy.

    The player's group's contribution is removed from the full syndrome.
    Removing the player's hat from the group's parity leaves exactly the
    visible hats in that group.  Thus the apparent use of the full input
    word in this computational implementation cancels the hidden bit.
    The exhaustive tests also check this cancellation directly.
    """
    parities, syndrome = group_state(word, gadget) if state is None else state
    column = gadget.pair_columns[position // 2]
    own_group_parity = parities[column - 1]
    visible_syndrome = syndrome ^ (column if own_group_parity else 0)

    if visible_syndrome == 0 or visible_syndrome == column:
        c = int(visible_syndrome == column)
        other_hats_in_group = own_group_parity ^ ((word >> position) & 1)
        return other_hats_in_group ^ (1 - c)

    mate_hat = (word >> (position ^ 1)) & 1
    return mate_hat ^ (position & 1)


def visible_pair_prediction(word: int, position: int, gadget: Gadget) -> int:
    """Independent implementation using only a player's visible hats.

    This formulation excludes only the player's own mate-pair, rather than
    its entire repeated-column group.  Every other pair contributes its
    own XOR parity times its column.  The remaining visible own-pair hat
    is the player's mate.  The function never examines bit ``position``.
    """
    own_pair = position // 2
    own_column = gadget.pair_columns[own_pair]
    visible_syndrome = 0
    for pair, column in enumerate(gadget.pair_columns):
        if pair == own_pair:
            continue
        first_hat = (word >> (2 * pair)) & 1
        second_hat = (word >> (2 * pair + 1)) & 1
        if first_hat ^ second_hat:
            visible_syndrome ^= column

    mate_hat = (word >> (position ^ 1)) & 1
    if visible_syndrome == 0:
        return mate_hat ^ 1
    if visible_syndrome == own_column:
        return mate_hat
    return mate_hat ^ (position & 1)


def rational_record(value: Fraction | int) -> dict[str, Any]:
    value = Fraction(value)
    return {
        "numerator": value.numerator,
        "denominator": value.denominator,
        "exact": str(value),
        "decimal": float(value),
    }


def hats_in_player_order(word: int, n: int) -> str:
    return "".join(str((word >> i) & 1) for i in range(n))


def fail(message: str, gadget: Gadget, word: int, **details: Any) -> None:
    record = {
        "message": message,
        "r": gadget.r,
        "a": gadget.a,
        "word_integer": word,
        "hats_in_player_order": hats_in_player_order(word, gadget.n),
        **details,
    }
    raise VerificationFailure(json.dumps(record, sort_keys=True))


def verify_case(r: int, a: int) -> dict[str, Any]:
    gadget = Gadget.create(r, a)
    start = time.perf_counter()
    t, n = gadget.t, gadget.n
    input_count = 1 << n
    good_score = n // 2 + a
    syndrome_counts: Counter[int] = Counter()
    score_counts: Counter[int] = Counter()
    player_correct_counts = [0] * n
    player_prediction_one_counts = [0] * n
    prefix_checks = 0
    min_error_numerator = 0
    max_error_numerator = 0
    max_abs_error_numerator = 0
    worst_witness: dict[str, Any] | None = None

    for word in range(input_count):
        state = group_state(word, gadget)
        _, syndrome = state
        syndrome_counts[syndrome] += 1
        good = syndrome != 0
        cumulative_correct = 0

        # The empty prefix has discrepancy zero and is included in the
        # reported prefix-check count on each good input.
        if good:
            prefix_checks += 1

        for position in range(n):
            guess = group_prediction(word, position, gadget, state)
            independent_guess = visible_pair_prediction(word, position, gadget)
            if guess != independent_guess:
                fail("prediction implementations disagree", gadget, word,
                     position=position, group_guess=guess,
                     visible_pair_guess=independent_guess)

            toggled_word = word ^ (1 << position)
            toggled_group_guess = group_prediction(toggled_word, position, gadget)
            if toggled_group_guess != guess:
                fail("whole-group implementation uses the hidden hat", gadget,
                     word, position=position, original=guess,
                     toggled=toggled_group_guess)
            toggled_pair_guess = visible_pair_prediction(
                toggled_word, position, gadget)
            if toggled_pair_guess != independent_guess:
                fail("visible-pair implementation uses the hidden hat", gadget,
                     word, position=position, original=independent_guess,
                     toggled=toggled_pair_guess)

            hat = (word >> position) & 1
            correct = int(guess == hat)
            player_correct_counts[position] += correct
            player_prediction_one_counts[position] += guess
            cumulative_correct += correct

            if good:
                u = position + 1
                # This is 2*t times (D_u - u/(2*t)).  No floating-point
                # approximation is used to decide whether a bound holds.
                error_numerator = 2 * t * cumulative_correct - u * (t + 1)
                prefix_checks += 1
                if abs(error_numerator) > 3 * t:
                    fail("good-input prefix bound exceeds 3/2", gadget, word,
                         prefix_length=u, cumulative_correct=cumulative_correct,
                         error_numerator=error_numerator,
                         error_denominator=2 * t)
                min_error_numerator = min(min_error_numerator, error_numerator)
                max_error_numerator = max(max_error_numerator, error_numerator)
                if (worst_witness is None
                        or abs(error_numerator) > max_abs_error_numerator):
                    max_abs_error_numerator = abs(error_numerator)
                    worst_witness = {
                        "word_integer": word,
                        "hats_in_player_order": hats_in_player_order(word, n),
                        "syndrome": syndrome,
                        "prefix_length": u,
                        "cumulative_correct": cumulative_correct,
                        "error": rational_record(Fraction(error_numerator, 2*t)),
                    }

        expected_score = good_score if good else 0
        if cumulative_correct != expected_score:
            fail("incorrect endpoint score", gadget, word,
                 syndrome=syndrome, expected=expected_score,
                 observed=cumulative_correct)
        score_counts[cumulative_correct] += 1

    uniform_syndrome_count = input_count // (t + 1)
    expected_syndromes = {s: uniform_syndrome_count for s in range(t + 1)}
    if dict(syndrome_counts) != expected_syndromes:
        raise VerificationFailure("The enumerated syndrome distribution is not uniform")
    expected_scores = {0: uniform_syndrome_count,
                       good_score: t * uniform_syndrome_count}
    if dict(score_counts) != expected_scores:
        raise VerificationFailure("The enumerated score distribution is incorrect")
    if any(count != input_count // 2 for count in player_correct_counts):
        raise VerificationFailure("An individual player's correctness marginal is not 1/2")
    if any(count != input_count // 2 for count in player_prediction_one_counts):
        raise VerificationFailure("An individual player's prediction is not balanced")

    expected_correct = sum(Fraction(score * count, input_count)
                           for score, count in score_counts.items())
    expected_surplus_squared = sum(
        Fraction((2*score - n)**2 * count, 4 * input_count)
        for score, count in score_counts.items())
    if expected_correct != Fraction(n, 2):
        raise VerificationFailure("The expected finite score is not N/2")
    if expected_surplus_squared != a*a*t:
        raise VerificationFailure("The second moment of endpoint surplus is not a^2*t")

    good_inputs = t * uniform_syndrome_count
    if prefix_checks != good_inputs * (n + 1):
        raise VerificationFailure("Internal prefix accounting failure")

    return {
        "parameters": {"r": r, "a": a, "t": t, "N": n},
        "status": "passed",
        "exhaustive_input_count": input_count,
        "individual_prediction_crosschecks": input_count * n,
        "own_hat_toggle_checks_per_implementation": input_count * n,
        "own_hat_toggle_checks_total": 2 * input_count * n,
        "good_prefix_checks_including_empty_prefix": prefix_checks,
        "syndrome_counts": dict(sorted(syndrome_counts.items())),
        "score_counts": dict(sorted(score_counts.items())),
        "good_input_count": good_inputs,
        "bad_input_count": uniform_syndrome_count,
        "good_probability": rational_record(Fraction(t, t + 1)),
        "bad_probability": rational_record(Fraction(1, t + 1)),
        "good_endpoint_surplus": a,
        "bad_endpoint_surplus": -a*t,
        "player_correct_counts": player_correct_counts,
        "player_prediction_one_counts": player_prediction_one_counts,
        "expected_correct_guesses": rational_record(expected_correct),
        "expected_endpoint_surplus": rational_record(expected_correct-Fraction(n, 2)),
        "expected_endpoint_surplus_squared": rational_record(expected_surplus_squared),
        "prefix_error_denominator_used_for_checks": 2*t,
        "asserted_prefix_absolute_error_bound": rational_record(Fraction(3, 2)),
        "observed_minimum_prefix_error": rational_record(Fraction(min_error_numerator, 2*t)),
        "observed_maximum_prefix_error": rational_record(Fraction(max_error_numerator, 2*t)),
        "observed_maximum_absolute_prefix_error": rational_record(
            Fraction(max_abs_error_numerator, 2*t)),
        "maximum_error_witness": worst_witness,
        "elapsed_seconds": round(time.perf_counter() - start, 6),
    }


def example_record(gadget: Gadget, word: int, name: str) -> dict[str, Any]:
    state = group_state(word, gadget)
    parities, syndrome = state
    guesses = [group_prediction(word, i, gadget, state) for i in range(gadget.n)]
    hats = [(word >> i) & 1 for i in range(gadget.n)]
    rows: list[dict[str, Any]] = []
    correct_count = 0
    for u in range(gadget.n + 1):
        if u:
            correct_count += int(hats[u-1] == guesses[u-1])
        surplus = Fraction(2*correct_count-u, 2)
        reference = Fraction(u, 2*gadget.t)
        rows.append({
            "prefix_length": u,
            "cumulative_correct": correct_count,
            "surplus": rational_record(surplus),
            "good_input_reference": rational_record(reference),
            "error_from_good_input_reference": rational_record(surplus-reference),
        })
    return {
        "name": name,
        "parameters": {"r": gadget.r, "a": gadget.a, "t": gadget.t, "N": gadget.n},
        "word_integer": word,
        "hats_in_player_order": hats_in_player_order(word, gadget.n),
        "group_parities": list(parities),
        "syndrome": syndrome,
        "is_good": syndrome != 0,
        "players": [
            {
                "position": i,
                "round": gadget.coordinates(i)[0],
                "column": gadget.coordinates(i)[1],
                "mate": gadget.coordinates(i)[2],
                "hat": hats[i],
                "guess": guesses[i],
                "correct": int(hats[i] == guesses[i]),
            }
            for i in range(gadget.n)
        ],
        "prefixes": rows,
        "reference_scope": (
            "The line u/(2*t) and its 3/2 discrepancy bound apply only to good inputs; "
            "the same line is included on bad examples for comparison, not as a claim."
        ),
    }


def write_examples(output_directory: Path) -> dict[str, str]:
    gadget = Gadget.create(2, 2)
    # Begin with (0,1) on every pair.  Since a=2, every group then has even
    # parity.  Toggle the first hat of column 3 in round 0 to make S=3.
    base_word = sum(1 << (2*pair+1) for pair in range(gadget.a*gadget.t))
    good_word = base_word ^ (1 << (2*(gadget.t-1)))
    good_example = example_record(gadget, good_word, "good_syndrome_3")
    bad_example = example_record(gadget, base_word, "bad_syndrome_0")
    examples_path = output_directory / "examples.json"
    examples_path.write_text(
        json.dumps({"examples": [good_example, bad_example]}, indent=2) + "\n",
        encoding="utf-8")

    csv_path = output_directory / "example_prefix.csv"
    with csv_path.open("w", encoding="utf-8", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=[
            "prefix_length", "cumulative_correct", "surplus", "reference", "error",
            "surplus_exact", "reference_exact", "error_exact",
        ])
        writer.writeheader()
        for row in good_example["prefixes"]:
            writer.writerow({
                "prefix_length": row["prefix_length"],
                "cumulative_correct": row["cumulative_correct"],
                "surplus": row["surplus"]["decimal"],
                "reference": row["good_input_reference"]["decimal"],
                "error": row["error_from_good_input_reference"]["decimal"],
                "surplus_exact": row["surplus"]["exact"],
                "reference_exact": row["good_input_reference"]["exact"],
                "error_exact": row["error_from_good_input_reference"]["exact"],
            })
    return {"examples_json": examples_path.name, "good_prefix_csv": csv_path.name}


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--case", nargs=2, type=int, action="append", metavar=("R", "A"),
                        help="verify this case (repeatable); default: nine cases with N <= 18")
    parser.add_argument("--max-n", type=int, default=18,
                        help="reject larger exhaustive cases unless this limit is raised (default: 18)")
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parent.parent / "data" / "verification.json",
                        help="path for the machine-readable verification report")
    parser.add_argument("--quiet", action="store_true", help="suppress per-case progress")
    args = parser.parse_args(argv)

    cases = [tuple(case) for case in args.case] if args.case else list(DEFAULT_CASES)
    cases = list(dict.fromkeys(cases))
    for r, a in cases:
        try:
            gadget = Gadget.create(r, a)
        except ValueError as error:
            parser.error(str(error))
        if gadget.n > args.max_n:
            parser.error(f"case (r={r}, a={a}) has N={gadget.n}, exceeding --max-n={args.max_n}")

    start = time.perf_counter()
    results = []
    for r, a in cases:
        result = verify_case(r, a)
        results.append(result)
        if not args.quiet:
            parameters = result["parameters"]
            print(
                f"PASS r={r}, a={a}, N={parameters['N']}: "
                f"{result['exhaustive_input_count']:,} inputs; "
                f"max prefix error {result['observed_maximum_absolute_prefix_error']['exact']}; "
                f"{result['elapsed_seconds']:.3f}s", flush=True)

    args.output.parent.mkdir(parents=True, exist_ok=True)
    example_files = write_examples(args.output.parent)
    report = {
        "artifact": "Exhaustive verification of finite interleaved binary hat gadgets",
        "version": 1,
        "status": "all requested finite cases passed",
        "scope": (
            "Exhaustive checks of the explicitly listed finite instances only. "
            "This is not machine verification of the infinite theorem or of the "
            "finite statements for all parameters."
        ),
        "completed_at_utc": datetime.now(timezone.utc).isoformat(),
        "runtime": {"implementation": platform.python_implementation(),
                    "python_version": platform.python_version()},
        "bit_convention": "bit i is physical player i; displayed hat strings run from bit 0 upward",
        "physical_order": "round 0..a-1, column 1..t, mate 0,1",
        "discrepancy_definition": "D_u = C_u-u/2; error = D_u-u/(2*t) on nonzero-syndrome inputs",
        "exact_prefix_test": "abs(2*t*C_u-u*(t+1)) <= 3*t",
        "independent_implementations": [
            "whole repeated-column group parity",
            "directly visible other-pair parity and own mate",
        ],
        "verification_summary": {
            "case_count": len(results),
            "exhaustive_input_count": sum(r["exhaustive_input_count"] for r in results),
            "individual_prediction_crosschecks": sum(
                r["individual_prediction_crosschecks"] for r in results),
            "own_hat_toggle_checks_per_implementation": sum(
                r["own_hat_toggle_checks_per_implementation"] for r in results),
            "own_hat_toggle_checks_total": sum(r["own_hat_toggle_checks_total"] for r in results),
            "good_prefix_checks_including_empty_prefix": sum(
                r["good_prefix_checks_including_empty_prefix"] for r in results),
            "elapsed_seconds": round(time.perf_counter() - start, 6),
        },
        "cases": results,
        "example_files": example_files,
    }
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    summary = report["verification_summary"]
    print(
        f"Verified {summary['case_count']} cases, "
        f"{summary['exhaustive_input_count']:,} inputs, "
        f"{summary['individual_prediction_crosschecks']:,} individual crosschecks, "
        f"{summary['own_hat_toggle_checks_total']:,} own-hat toggle checks.\n"
        f"Report: {args.output.resolve()}", flush=True)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except VerificationFailure as error:
        print(f"VERIFICATION FAILED: {error}", file=sys.stderr)
        raise SystemExit(1) from error
