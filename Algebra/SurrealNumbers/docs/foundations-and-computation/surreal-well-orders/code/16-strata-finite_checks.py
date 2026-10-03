#!/usr/bin/env python3
"""Run finite diagnostics, not transfinite proofs or formal verification.

Uses only the Python standard library. Finite surreal sign strings are evaluated
independently as exact dyadic rationals: an initial constant run of length k
contributes +/-k, and later zero-based position i has weight 2**(-(i-k+1)).
No lexicographic comparator on encoded sign strings is used to assess their
numerical order. The raw-order diagnostic evaluates the predecessor predicate
on relation matrices and compares its result with enumeration lexicography.

Run ``python3 finite_checks.py`` to regenerate finite_check_results.json beside
this script. An optional ``--output PATH`` selects a different results file.
"""

from __future__ import annotations

import argparse
import json
import sys
from fractions import Fraction
from itertools import permutations, product
from pathlib import Path
from typing import Callable, Sequence


Signs = tuple[int, ...]
Word = tuple[int, ...]
Relation = tuple[tuple[bool, ...], ...]


def require(condition: bool, message: str) -> None:
    """Keep diagnostics enabled even when Python is run with optimization."""
    if not condition:
        raise AssertionError(message)


def compare(left: object, right: object) -> int:
    return int(left > right) - int(left < right)


def finite_surreal_value(signs: Signs) -> Fraction:
    """Evaluate finite signs by the initial-run dyadic formula, not by lex."""
    if not signs:
        return Fraction(0)
    require(all(sign in (-1, 1) for sign in signs), "Invalid surreal sign")
    initial = signs[0]
    run_length = 1
    while run_length < len(signs) and signs[run_length] == initial:
        run_length += 1
    value = Fraction(initial * run_length)
    for position in range(run_length, len(signs)):
        denominator = 2 ** (position - run_length + 1)
        value += Fraction(signs[position], denominator)
    return value


def check_numeric_evaluator() -> dict:
    """Known finite numbers guard sign and exponent indexing conventions."""
    examples = [
        ((), Fraction(0)),
        ((1,), Fraction(1)),
        ((-1, -1), Fraction(-2)),
        ((1, -1), Fraction(1, 2)),
        ((1, -1, 1), Fraction(3, 4)),
        ((1, 1, -1), Fraction(3, 2)),
        ((-1, -1, 1), Fraction(-3, 2)),
        ((-1, 1, 1), Fraction(-1, 4)),
    ]
    for signs, expected in examples:
        actual = finite_surreal_value(signs)
        require(actual == expected, f"Numeric evaluator: {signs}: {actual} != {expected}")
    return {
        "status": "passed",
        "known_value_checks": len(examples),
        "arithmetic": "fractions.Fraction; exact dyadic rationals",
        "encoded_sign_lex_comparator_used": False,
    }


def epsilon_against_letter(value: Fraction, convention: str) -> int:
    """Return the sign of formal epsilon compared with one numerical letter."""
    if convention == "zero_before":
        return 1 if value < 0 else -1
    if convention == "zero_after":
        return 1 if value <= 0 else -1
    if convention == "prefix_first":
        return -1
    raise ValueError(f"Unknown convention: {convention}")


def compare_words(
    left: Word,
    right: Word,
    letter_values: Sequence[Fraction],
    convention: str,
) -> int:
    """Compare input words using numerical letters and a formal terminator."""
    common_length = min(len(left), len(right))
    for position in range(common_length):
        relation = compare(letter_values[left[position]], letter_values[right[position]])
        if relation:
            return relation
    if len(left) == len(right):
        return 0
    if len(left) < len(right):
        return epsilon_against_letter(letter_values[right[common_length]], convention)
    return -epsilon_against_letter(letter_values[left[common_length]], convention)


def doubled(signs: Signs) -> Signs:
    return tuple(sign for old_sign in signs for sign in (old_sign, old_sign))


def c_minus(signs: Signs) -> Signs:
    return doubled(signs) + (1, -1)


def c_plus(signs: Signs) -> Signs:
    return doubled(signs) + (-1, 1)


def prefix_first_c_minus(signs: Signs) -> Signs:
    return (1,) + c_minus(signs)


def prefix_first_c_plus(signs: Signs) -> Signs:
    return (1,) + c_plus(signs)


def encode_word(word: Word, letter_codes: Sequence[Signs]) -> Signs:
    return tuple(sign for letter in word for sign in letter_codes[letter])


def check_code_scheme(
    name: str,
    formula: str,
    convention: str,
    code: Callable[[Signs], Signs],
    alphabet: Sequence[Signs],
    letter_values: Sequence[Fraction],
    words: Sequence[Word],
) -> dict:
    codes = [code(signs) for signs in alphabet]
    require(len(set(codes)) == len(codes), f"{name}: letter codes are not injective")
    code_values = [finite_surreal_value(signs) for signs in codes]
    require(
        len(set(code_values)) == len(codes),
        f"{name}: distinct letter codes have equal numerical values",
    )

    prefix_checks = 0
    letter_comparisons = 0
    for i, left_code in enumerate(codes):
        for j, right_code in enumerate(codes):
            if i != j:
                prefix_checks += 1
                require(
                    left_code != right_code[: len(left_code)],
                    f"{name}: letter {i} is a prefix of letter {j}",
                )
            letter_comparisons += 1
            require(
                compare(code_values[i], code_values[j])
                == compare(letter_values[i], letter_values[j]),
                f"{name}: letter order disagreement at {i}, {j}",
            )

    images = [encode_word(word, codes) for word in words]
    image_values = [finite_surreal_value(signs) for signs in images]
    require(len(set(images)) == len(words), f"{name}: word sign codes are not injective")
    require(
        len(set(image_values)) == len(words),
        f"{name}: word numerical images are not injective",
    )
    require(image_values[0] == 0, f"{name}: empty word must encode zero")
    if convention == "prefix_first":
        require(
            all(value > 0 for value in image_values[1:]),
            f"{name}: a nonempty prefix-first word has a nonpositive image",
        )

    word_comparisons = 0
    for i, left in enumerate(words):
        for j, right in enumerate(words):
            word_comparisons += 1
            expected = compare_words(left, right, letter_values, convention)
            actual = compare(image_values[i], image_values[j])
            require(
                actual == expected,
                f"{name}: {left} vs {right}: numeric sign {actual}, word sign {expected}",
            )

    return {
        "name": name,
        "formula": formula,
        "terminator": convention,
        "status": "passed",
        "letters": len(alphabet),
        "words": len(words),
        "letter_prefix_freeness_checks_ordered_distinct": prefix_checks,
        "letter_order_comparisons_ordered_including_equal": letter_comparisons,
        "word_order_comparisons_ordered_including_equal": word_comparisons,
        "word_order_comparisons_ordered_distinct": word_comparisons - len(words),
        "distinct_word_sign_codes": len(set(images)),
        "distinct_word_numeric_values": len(set(image_values)),
        "maximum_encoded_sign_length": max(map(len, images)),
    }


def check_sign_codes() -> dict:
    alphabet = [
        tuple(signs)
        for length in range(4)
        for signs in product((-1, 1), repeat=length)
    ]
    letter_values = [finite_surreal_value(signs) for signs in alphabet]
    require(len(set(letter_values)) == len(alphabet), "Input sign values are not distinct")
    words = [
        tuple(word)
        for length in range(3)
        for word in product(range(len(alphabet)), repeat=length)
    ]
    schemes = [
        ("centered_c_minus", "D(s) + (+,-)", "zero_before", c_minus),
        ("centered_c_plus", "D(s) + (-,+)", "zero_after", c_plus),
        (
            "prefix_first_from_c_minus",
            "(+) + D(s) + (+,-)",
            "prefix_first",
            prefix_first_c_minus,
        ),
        (
            "prefix_first_from_c_plus",
            "(+) + D(s) + (-,+)",
            "prefix_first",
            prefix_first_c_plus,
        ),
    ]
    results = [
        check_code_scheme(name, formula, convention, code, alphabet, letter_values, words)
        for name, formula, convention, code in schemes
    ]
    return {
        "status": "passed",
        "maximum_input_sign_length": 3,
        "maximum_word_length": 2,
        "input_alphabet_size": len(alphabet),
        "input_word_count": len(words),
        "scheme_count": len(results),
        "schemes": results,
        "totals": {
            "letter_prefix_freeness_checks": sum(
                item["letter_prefix_freeness_checks_ordered_distinct"] for item in results
            ),
            "letter_order_comparisons": sum(
                item["letter_order_comparisons_ordered_including_equal"] for item in results
            ),
            "word_order_comparisons": sum(
                item["word_order_comparisons_ordered_including_equal"] for item in results
            ),
        },
    }


def relation_from_enumeration(enumeration: tuple[int, ...]) -> Relation:
    """Create a strict relation matrix; all later raw tests use only the matrix."""
    positions = {label: index for index, label in enumerate(enumeration)}
    return tuple(
        tuple(positions[left] < positions[right] for right in range(len(enumeration)))
        for left in range(len(enumeration))
    )


def raw_predecessor_pairs(left: Relation, right: Relation) -> list[tuple[int, int]]:
    """Evaluate the raw predecessor formula directly, with a != b.

    For every z: z R a iff z S b.
    For x,y R a: x R y iff x S y.
    """
    size = len(left)
    require(len(right) == size, "Relations have different carriers")
    witnesses = []
    for a in range(size):
        for b in range(size):
            if a == b:
                continue
            if not all(left[z][a] == right[z][b] for z in range(size)):
                continue
            predecessors = [x for x in range(size) if left[x][a]]
            if all(left[x][y] == right[x][y] for x in predecessors for y in predecessors):
                witnesses.append((a, b))
    return witnesses


def check_raw_predecessor_formula() -> dict:
    by_size = []
    for size in range(6):
        enumerations = list(permutations(range(size)))
        relations = [relation_from_enumeration(p) for p in enumerations]
        compared = 0
        distinct = 0
        equal = 0
        for i, left in enumerate(enumerations):
            for j, right in enumerate(enumerations):
                compared += 1
                candidates = raw_predecessor_pairs(relations[i], relations[j])
                expected = compare(left, right)
                if expected == 0:
                    equal += 1
                    require(not candidates, f"n={size}: equal raw orders have a witness")
                    actual = 0
                else:
                    distinct += 1
                    require(
                        len(candidates) == 1,
                        f"n={size}: {left}, {right}: nonunique raw witnesses {candidates}",
                    )
                    a, b = candidates[0]
                    actual = compare(a, b)
                    first = next(k for k in range(size) if left[k] != right[k])
                    require(
                        (a, b) == (left[first], right[first]),
                        f"n={size}: raw witness does not give the first differing labels",
                    )
                    predecessor_set = {z for z in range(size) if relations[i][z][a]}
                    require(
                        predecessor_set == set(left[:first]),
                        f"n={size}: raw common prefix differs from enumeration prefix",
                    )
                require(
                    actual == expected,
                    f"n={size}: raw comparison disagrees for {left} and {right}",
                )
        by_size.append(
            {
                "n": size,
                "permutations": len(enumerations),
                "ordered_relation_pairs_including_equal": compared,
                "distinct_ordered_pairs_with_unique_witness": distinct,
                "equal_pairs_with_no_witness": equal,
                "distinct_label_pairs_submitted_to_predicate": compared * size * (size - 1),
            }
        )
    return {
        "status": "passed",
        "minimum_n": 0,
        "maximum_n": 5,
        "by_size": by_size,
        "totals": {
            "permutation_instances": sum(item["permutations"] for item in by_size),
            "ordered_relation_pair_comparisons": sum(
                item["ordered_relation_pairs_including_equal"] for item in by_size
            ),
            "unique_witness_checks_for_distinct_pairs": sum(
                item["distinct_ordered_pairs_with_unique_witness"] for item in by_size
            ),
            "equal_pairs_checked": sum(item["equal_pairs_with_no_witness"] for item in by_size),
            "distinct_label_pairs_submitted_to_predicate": sum(
                item["distinct_label_pairs_submitted_to_predicate"] for item in by_size
            ),
        },
    }


def check_relation_table_counterexample() -> dict:
    left = (0, 2, 1)
    right = (1, 0, 2)
    left_relation = relation_from_enumeration(left)
    right_relation = relation_from_enumeration(right)
    pair_order = list(product(range(3), repeat=2))
    left_bits = tuple(int(left_relation[a][b]) for a, b in pair_order)
    right_bits = tuple(int(right_relation[a][b]) for a, b in pair_order)
    first = next(i for i in range(len(pair_order)) if left_bits[i] != right_bits[i])
    enumeration_comparison = compare(left, right)
    table_comparison = compare(left_bits, right_bits)
    raw_pairs = raw_predecessor_pairs(left_relation, right_relation)
    require(enumeration_comparison == -1, "Counterexample has wrong enumeration comparison")
    require(table_comparison == 1, "Counterexample has wrong relation-table comparison")
    require(pair_order[first] == (0, 1), "Counterexample has wrong first table difference")
    require((left_bits[first], right_bits[first]) == (1, 0), "Counterexample has wrong bits")
    require(raw_pairs == [(0, 1)], "Counterexample has wrong raw comparison witness")
    return {
        "status": "passed",
        "f": list(left),
        "g": list(right),
        "table_pair_order": "row-major (a,b), a outer; strict relation; 0 < 1",
        "f_relation_bits": list(left_bits),
        "g_relation_bits": list(right_bits),
        "first_differing_table_pair": list(pair_order[first]),
        "first_differing_bits": [left_bits[first], right_bits[first]],
        "enumeration_comparison_sign": enumeration_comparison,
        "raw_predecessor_comparison_sign": compare(*raw_pairs[0]),
        "relation_table_comparison_sign": table_comparison,
        "opposite_comparisons_verified": True,
    }


def run_all() -> dict:
    evaluator = check_numeric_evaluator()
    sign_codes = check_sign_codes()
    raw = check_raw_predecessor_formula()
    counterexample = check_relation_table_counterexample()
    return {
        "schema_version": 1,
        "status": "passed",
        "scope": "Finite diagnostics only; not transfinite proofs or formal verification.",
        "runtime": "Python standard library only",
        "numeric_evaluator": evaluator,
        "sign_code_checks": sign_codes,
        "raw_predecessor_formula": raw,
        "relation_table_counterexample": counterexample,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output",
        type=Path,
        default=Path(__file__).resolve().with_name("finite_check_results.json"),
        help="JSON results path (default: beside this script)",
    )
    args = parser.parse_args()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    try:
        result = run_all()
    except AssertionError as error:
        failure = {"schema_version": 1, "status": "failed", "error": str(error)}
        args.output.write_text(json.dumps(failure, indent=2) + "\n", encoding="utf-8")
        print(f"FAIL: {error}", file=sys.stderr)
        return 1
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    sign_totals = result["sign_code_checks"]["totals"]
    raw_totals = result["raw_predecessor_formula"]["totals"]
    print("PASS: 4 sign-code schemes; 15 letters; 241 words per scheme.")
    print(
        f"PASS: {sign_totals['word_order_comparisons']:,} ordered word-pair comparisons; "
        f"{sign_totals['letter_order_comparisons']:,} letter comparisons; "
        f"{sign_totals['letter_prefix_freeness_checks']:,} prefix-freeness checks."
    )
    print(
        f"PASS: {raw_totals['ordered_relation_pair_comparisons']:,} raw relation-pair comparisons "
        f"for n=0..5; {raw_totals['unique_witness_checks_for_distinct_pairs']:,} "
        "distinct pairs have their unique expected witness."
    )
    print("PASS: row-major relation-table counterexample reverses enumeration comparison.")
    print(f"Results: {args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
