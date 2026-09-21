"""Reproduce all finite tests. These are not a formal proof of infinite claims."""
from __future__ import annotations

import csv
import json
from fractions import Fraction
from itertools import product
from pathlib import Path
from time import perf_counter

from broadcast_finite import (apply, followers, game_value, legal, legal_actions,
                              power_and_upgrade, sign_strings, sign_value,
                              truncate)


def run() -> dict:
    start = perf_counter()
    counts: dict[str, int] = {}

    # One-string cuts are independent of order, even when an earlier cut erases
    # the other selected sign. Include idle thresholds and both sign choices.
    count = 0
    for s in sign_strings(8):
        for a, b in product('+-', repeat=2):
            for gamma, eta in product(range(len(s) + 1), repeat=2):
                lhs = truncate(truncate(s, a, gamma), b, eta)
                rhs = truncate(truncate(s, b, eta), a, gamma)
                assert lhs == rhs, (s, a, b, gamma, eta)
                count += 1
    counts['single_string_commutation_checks'] = count

    # Exact recursive values rather than simply using the finite-sum theorem.
    for arity, maximum in ((2, 4), (3, 3)):
        count = 0
        for state in product(sign_strings(maximum), repeat=arity):
            expected = sum((sign_value(s) for s in state), Fraction(0))
            assert game_value(state) == expected, state
            count += 1
        counts[f'finite_game_values_arity_{arity}_max_birthday_{maximum}'] = count

    # Check the diamond argument including finite exemptions and legal witnesses.
    count = 0
    for state in product(sign_strings(3), repeat=2):
        for gamma, f in legal_actions(state, '+'):
            lstate = apply(state, '+', gamma, f)
            for eta, h in legal_actions(state, '-'):
                rstate = apply(state, '-', eta, h)
                common = apply(lstate, '-', eta, h)
                assert common == apply(rstate, '+', gamma, f)
                if gamma <= eta:
                    assert legal(rstate, '+', gamma, f)
                if eta <= gamma:
                    assert legal(lstate, '-', eta, h)
                # The other action can be idle, or a legal move at a NEW threshold.
                assert common == lstate or common in followers(lstate, '-')
                assert common == rstate or common in followers(rstate, '+')
                assert game_value(lstate) < game_value(rstate)
                count += 1
    counts['legal_left_right_diamonds'] = count

    # Oddness, reindexing and zero padding for all small pairs.
    count = 0
    flip = str.maketrans('+-', '-+')
    for state in product(sign_strings(3), repeat=2):
        value = game_value(state)
        assert game_value(tuple(s.translate(flip) for s in state)) == -value
        assert game_value(tuple(reversed(state))) == value
        assert game_value(('',) + state) == value
        count += 1
    counts['structural_identity_triples_of_checks'] = count

    # The exact short-sign formula used in the infinite-family proof.
    count = 0
    for d in range(2, 9):
        for n in range(40):
            a, b = power_and_upgrade(n, d)
            assert sign_value(a) == Fraction(1, 2 ** (n + d))
            assert sign_value(b) == Fraction(3, 2 ** (n + d + 1))
            assert truncate(b, '+', n + d + 1) == a
            for gamma in range(1, n + d + 1):
                expected = '+' + '-' * (gamma - 1)
                assert truncate(a, '-', gamma) == expected
                assert truncate(b, '-', gamma) == expected
                count += 2
            count += 3
    counts['dyadic_sign_and_tail_checks'] = count

    output = Path(__file__).resolve().parents[1] / 'verification'
    output.mkdir(exist_ok=True)
    # Values in the last column are analytically proved in the manuscript, not
    # returned by game_value. Only finite partial sums are computational data.
    with (output / 'partial_sums.csv').open('w', newline='') as handle:
        writer = csv.writer(handle)
        writer.writerow(['number_of_terms', 'base_partial_sum_d2',
                         'all_upgraded_partial_sum_d2',
                         'infinite_base_value_from_theorem',
                         'infinite_upgraded_value_from_theorem'])
        for terms in range(1, 31):
            base = sum((Fraction(1, 2 ** (n + 2)) for n in range(terms)), Fraction(0))
            upgraded = base * Fraction(3, 2)
            writer.writerow([terms, str(base), str(upgraded), '1', 'sqrt(omega)'])

    report = {
        'result': 'PASS',
        'description': 'Exact finite tests of canonical sign truncations and game cuts',
        'counts': counts,
        'memoized_finite_states': game_value.cache_info().currsize,
        'elapsed_seconds': round(perf_counter() - start, 3),
        'arithmetic': 'Python fractions.Fraction; no floating-point comparisons',
        'scope_limit': ('Finite tests do not verify the transfinite rank theorem, '
                        'number-valuedness for arbitrary surreal inputs, or the '
                        'infinite dyadic-family formula. Those rely on the paper proofs.'),
    }
    (output / 'test_report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))
    return report


if __name__ == '__main__':
    run()
