#!/usr/bin/env python3
"""Finite standard-model checks for the scalar UR reflection derivation.

These checks detect algebraic and boundary transcription errors. They do not
prove the universal first-order metatheorem, the scalar predecessor bootstrap,
the admissibility of UR, or a checker/logic correspondence theorem.

The tested accumulator is evaluated by its explicit monus term. Its independent
oracle is a direct finite sum of ordinary comparisons, without using that term.
Only Python's standard library is required.
"""

import json
import platform
from collections import Counter
from pathlib import Path


def pred(n):
    return max(n - 1, 0)


def d(a, b):
    return max(a - b, 0)


def zero(n):
    return int(n == 0)


def sign(n):
    return int(n != 0)


def choose(n, a, b):
    return a if n == 0 else b


def bool_or(a, b):
    return choose(a, b, 1)


def bool_xor(a, b):
    return choose(a, b, zero(b))


def b1_left(n, a):
    return zero(d(n + 1, a))


def b1_right(n, a):
    return sign(d(a, n))


def q1(n, a):
    return bool_xor(b1_left(n, a), b1_right(n, a))


def b2_left(x, a, b):
    return zero(d(d(x, a), d(b, a)))


def b2_right(x, a, b):
    return bool_or(zero(d(x, a)), zero(d(x, b)))


def q2(x, a, b):
    return bool_xor(b2_left(x, a, b), b2_right(x, a, b))


def mu(n, a):
    return d(n, d(n, a))


def phi(n, a, b):
    return mu(n, a) + mu(d(n, a), d(b, a))


def max_term(a, b):
    return a + d(b, a)


def delta(a, b):
    return sign(d(a, b) + d(b, a))


def main():
    counts = Counter()

    def check(name, condition, data):
        counts[name] += 1
        if not condition:
            raise AssertionError((name, data))

    for p in range(2):
        for q in range(2):
            check("boolean_or", bool_or(p, q) == int(bool(p or q)), (p, q))
            check("boolean_xor", bool_xor(p, q) == int(p != q), (p, q))

    for n in range(65):
        for a in range(65):
            check("monus_successor_cancellation", d(n + 1, a + 1) == d(n, a), (n, a))
            check("monus_Pd", pred(d(n + 1, a)) == d(n, a), (n, a))
            check("B1", b1_left(n, a) == b1_right(n, a), (n, a))
            check("B1_successor_invariance", q1(n + 1, a + 1) == q1(n, a), (n, a))
            check("B1_predecessor_invariance", q1(pred(n), pred(a)) == q1(n, a), (n, a))
            check("mu_recurrence", mu(n + 1, a) == mu(n, a) + zero(d(n + 1, a)), (n, a))
            check("max_diagonal_reduction", max_term(n, a) == max_term(pred(n), pred(a)) + sign(n + a), (n, a))
            check("max_standard_oracle", max_term(n, a) == max(n, a), (n, a))
            check("actual_equality_reflection", (delta(n, a) == 0) == (n == a), (n, a))
            check("delta_boolean_range", delta(n, a) in (0, 1), (n, a))

    for x in range(33):
        for a in range(33):
            for b in range(33):
                check("B2", b2_left(x, a, b) == b2_right(x, a, b), (x, a, b))
                check("B2_successor_invariance", q2(x + 1, a + 1, b + 1) == q2(x, a, b), (x, a, b))
                check("B2_predecessor_invariance", q2(pred(x), pred(a), pred(b)) == q2(x, a, b), (x, a, b))
                # The chosen endpoint is the first parameter, exactly as in DD.
                check("B2_descent_endpoint", q2(d(x, x), d(a, x), d(b, x)) == 0, (x, a, b))
                if x == 0 or a == 0 or b == 0:
                    check("B2_zero_coordinate_boundary", q2(x, a, b) == 0, (x, a, b))

    for n in range(33):
        for a in range(33):
            for b in range(33):
                seed = d(b, a)
                local_bit = zero(d(d(n + 1, a), seed))
                increment = sign(d(a, n) + d(b, n))
                check("accumulator_local_recurrence", phi(n + 1, a, b) == phi(n, a, b) + local_bit, (n, a, b))
                check("accumulator_cutoff_identity", local_bit == increment, (n, a, b))
                check("accumulator_recurrence", phi(n + 1, a, b) == phi(n, a, b) + increment, (n, a, b))
                # Independent oracle: direct Python comparison, not truncated
                # subtraction, mu, maximum, or the tested closed scalar term.
                oracle = sum(int(i < a or i < b) for i in range(n))
                check("accumulator_independent_sum_oracle", phi(n, a, b) == oracle, (n, a, b))
                f = max_term(d(a, n), d(b, n)) + phi(n, a, b)
                g = max_term(d(b, n), d(a, n)) + phi(n, a, b)
                f_next = max_term(d(a, n + 1), d(b, n + 1)) + phi(n + 1, a, b)
                g_next = max_term(d(b, n + 1), d(a, n + 1)) + phi(n + 1, a, b)
                check("F_constant_recurrence", f_next == f, (n, a, b))
                check("G_constant_recurrence", g_next == g, (n, a, b))
                check("F_initial_value", f == max_term(a, b), (n, a, b))
                check("G_initial_value", g == max_term(b, a), (n, a, b))
                if n == b:
                    check("F_G_endpoint_agreement", f == g == d(a, b) + phi(b, a, b), (a, b))

    # Deliberate nearby transcription errors must be detected. The tiny first
    # counterexamples expose the importance of the future counter and cutoff.
    mutants = {}
    for n in range(5):
        for a in range(5):
            if mu(n + 1, a) != mu(n, a) + zero(d(n, a)):
                mutants.setdefault("mu_uses_current_instead_of_successor", [n, a])
            if zero(d(n, a)) != sign(d(a, n)):
                mutants.setdefault("B1_omits_successor", [n, a])
            for b in range(5):
                if b2_left(n, a, b) != zero(d(n, b)):
                    mutants.setdefault("B2_omits_first_or_disjunct", [n, a, b])
                bad_phi = mu(n, a) + mu(d(n, a), b)
                oracle = sum(int(i < a or i < b) for i in range(n))
                if bad_phi != oracle:
                    mutants.setdefault("accumulator_uses_b_instead_of_b_minus_a", [n, a, b])
    if len(mutants) != 4:
        raise AssertionError(("mutation_controls_not_all_detected", mutants))

    result = {
        "status": "passed",
        "python": platform.python_version(),
        "scope": "Finite standard-natural-number algebra checks; not a universal proof or proof-assistant verification.",
        "independent_oracle": "Direct finite sum sum(1 for i<n if i<a or i<b).",
        "bounds": {"binary_coordinates_inclusive": [0, 64], "ternary_coordinates_inclusive": [0, 32]},
        "checks": dict(sorted(counts.items())),
        "total_checks": sum(counts.values()),
        "unexpected_failures": 0,
        "deliberate_mutants_detected": mutants,
        "unverified_by_this_script": [
            "The universal written theorem and its contextual inference rules",
            "The independently required scalar predecessor term",
            "Soundness or completeness of any proof checker",
            "Bi-interpretation with full first-order iPRA"
        ]
    }
    output = Path(__file__).with_name("ur_reflection_validation.json")
    output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
