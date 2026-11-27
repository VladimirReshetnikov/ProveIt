#!/usr/bin/env python3
"""Reproduce the exact certificates in the accompanying paper.

Run from any working directory: python3 code/verify.py
Writes results/verification.json and results/phase_diagram.csv.
"""
from collections import Counter
from itertools import combinations
from pathlib import Path
import csv
import json
import random

from branch_recovery import (
    capacity, capacity_witness, contact_tree, decode_f2, encode_f2,
    evaluation_rows, f2_mul, greedy_spectrum, jet_recoverable_by_matrix,
    lt_contact, multiplicative_branch, recovery_cutoff, relative_distance,
    tree_spectrum,
)


def subsets(items):
    for length in range(len(items) + 1):
        yield from combinations(items, length)


def main():
    root = Path(__file__).resolve().parents[1]
    results = root / "results"
    results.mkdir(exist_ok=True)
    B = tuple(range(16))
    tree = contact_tree(B, lt_contact)
    assert tree_spectrum(tree) == greedy_spectrum(B, lt_contact)[1]

    # Exhaustive verification of the pruning DP against a different algorithm:
    # direct greedy spectra on every subset of an eight-leaf tree.
    small = tuple(range(8))
    small_tree = contact_tree(small, lt_contact)
    spectra = {}
    for S in subsets(small):
        spectrum = greedy_spectrum(S, lt_contact)[1]
        assert spectrum == tree_spectrum(small_tree, frozenset(S))
        assert all(b >= a + 1 for a, b in zip(spectrum, spectrum[1:]))
        spectra[S] = spectrum
    capacity_checks = 0
    for r in range(8):
        for threshold in range(30):
            expected = max(len(S) for S, spectrum in spectra.items()
                           if r >= len(S) or spectrum[r] >= threshold)
            actual = capacity(small_tree, r, threshold)
            assert actual == expected, (r, threshold, actual, expected)
            witness = capacity_witness(small_tree, r, threshold)
            ws = greedy_spectrum(witness, lt_contact)[1]
            assert len(witness) == actual
            assert r >= len(witness) or ws[r] >= threshold
            capacity_checks += 1

    # Main example: every ten-element surviving set, not just selected examples.
    hist = Counter()
    maximizing = []
    for S in combinations(B, 10):
        value = greedy_spectrum(S, lt_contact, limit=6)[1][5]
        hist[value] += 1
        if value == 14:
            maximizing.append(S)
    assert sum(hist.values()) == 8008
    assert max(hist) == 14
    S_A = (0, 1, 2, 4, 5, 8, 9, 10, 12, 13)
    S_P = (0, 2, 4, 6, 8, 10, 12, 14, 1, 9)
    order_A, profile_A = greedy_spectrum(S_A, lt_contact)
    _, profile_P = greedy_spectrum(S_P, lt_contact)
    assert profile_A == [0, 1, 3, 6, 8, 14, 16, 19, 21, 24]
    assert profile_P == [0, 1, 3, 7, 9, 12, 18, 20, 24, 26]
    assert capacity(tree, 5, 14) == 10
    assert capacity(tree, 5, 15) == 9
    child9 = [capacity(tree.children[0], r, 9) for r in range(6)]
    child10 = [capacity(tree.children[0], r, 10) for r in range(6)]
    assert child9 == [0, 1, 4, 6, 8, 8]
    assert child10 == [0, 1, 4, 5, 8, 8]

    # Independent linear algebra on actual formal branch substitutions, including
    # unknown terms of every total degree below the observation cutoff.
    matrix_checks = []
    check_sets = [(0, 1), (0, 2), (0, 1, 4), (0, 2, 4, 6),
                  (0, 1, 2, 3, 4, 5, 6, 7), S_A, S_P]
    for S in check_sets:
        d = min(len(S), 6)
        cost = greedy_spectrum(S, lt_contact, limit=d)[1][-1]
        for n in sorted({max(d, cost), cost + 1}):
            actual = jet_recoverable_by_matrix(S, d, n)
            expected = n > cost
            assert actual == expected, (S, d, n, actual, expected)
            matrix_checks.append({"labels": S, "d": d, "n": n,
                                  "recoverable": actual})

    # Sharp algebraic obstruction at n=14: product of five branch factors.
    roots = tuple(order_A[:5])
    assert roots == (0, 1, 2, 5, 4)
    word14 = {}
    orders = {}
    for b in B:
        image = 1
        for a in roots:
            image = f2_mul(image, multiplicative_branch(b, 32)
                          ^ multiplicative_branch(a, 32), 32)
        word14[b] = image & ((1 << 14) - 1)
        orders[b] = None if image == 0 else (image & -image).bit_length() - 1
    zeros14 = tuple(b for b in B if word14[b] == 0)
    support14 = tuple(b for b in B if word14[b] != 0)
    assert zeros14 == S_A
    assert support14 == (3, 6, 7, 11, 14, 15)
    # The received word is within three corruptions of both 0 and H.
    received_ambiguous = {b: word14[b] if b in support14[:3] else 0 for b in B}
    distance_to_zero = sum(bool(v) for v in received_ambiguous.values())
    distance_to_H = sum(received_ambiguous[b] != word14[b] for b in B)
    assert (distance_to_zero, distance_to_H) == (3, 3)

    # Actual reference decoding at the sharp sufficient cutoff n=15.
    mons, blocks = evaluation_rows(B, 15)
    rng = random.Random(20261126)
    true_polynomial = rng.getrandbits(len(mons))
    correct = encode_f2(true_polynomial, blocks)
    corrupt = {0: 0b100110111001011, 7: 0b101011100110101, 15: 0b111000101001101}
    received = {b: value ^ corrupt.get(b, 0) for b, value in correct.items()}
    decoded = decode_f2(received, d=6, n=15, errors=3, check_all=True)
    expected_jet = true_polynomial & ((1 << 21) - 1)
    assert decoded["candidate_jet_bitsets"] == [expected_jet]
    assert decoded["systems_examined"] == 560
    assert tuple(corrupt) in [tuple(x) for x in decoded["consistent_error_location_sets"]]
    # Regression for a genuine ambiguity: H=Y is invisible on branches 0,2
    # at precision2. A free-variable-zero solution must not masquerade as unique.
    guard_rejected = False
    try:
        decode_f2({0: 0, 2: 0}, d=2, n=2, errors=0, check_all=True)
    except ValueError:
        guard_rejected = True
    assert guard_rejected

    # Saturation formula and the complete distance/precision diagram.
    saturation = 1 + 5 + sum((2**h - 2**(h - 1)) * min(5, 2**(4 - h) - 1)
                              for h in range(1, 4))
    assert saturation == 21
    phase = [{"precision": n, "max_zero_branches": capacity(tree, 5, n),
              "relative_distance": relative_distance(tree, 6, n),
              "max_errors_no_erasures": max(-1, (relative_distance(tree, 6, n) - 1) // 2)}
             for n in range(28)]
    with (results / "phase_diagram.csv").open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=phase[0].keys())
        writer.writeheader()
        writer.writerows(phase)

    summary = {
        "status": "all checks passed",
        "arithmetic": "exact integers and F2; no floating-point arithmetic",
        "small_tree_subsets": len(spectra),
        "capacity_checks_against_exhaustive_subsets": capacity_checks,
        "ten_survivor_subsets": sum(hist.values()),
        "sixth_factorial_histogram": dict(sorted(hist.items())),
        "worst_sixth_factorial": max(hist),
        "number_of_maximizing_ten_subsets": len(maximizing),
        "adversarial_subset": S_A,
        "adversarial_greedy_order": order_A,
        "adversarial_spectrum": profile_A,
        "packed_subset": S_P,
        "packed_spectrum": profile_P,
        "child_capacity_threshold9": child9,
        "child_capacity_threshold10": child10,
        "matrix_checks": matrix_checks,
        "sharpness_roots": roots,
        "sharpness_branch_orders": orders,
        "sharpness_zero_set_at14": zeros14,
        "ambiguous_word_at14": received_ambiguous,
        "ambiguous_word_distances": [distance_to_zero, distance_to_H],
        "decoder_demo": decoded,
        "decoder_demo_true_jet_bitset": expected_jet,
        "decoder_rejects_uncertified_ambiguity": guard_rejected,
        "pure_error_cutoffs": {str(t): recovery_cutoff(tree, 6, t) for t in range(6)},
        "saturation_precision": saturation,
        "finite_checks_are_not_a_formal_proof": True,
    }
    (results / "verification.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps({k: summary[k] for k in (
        "status", "capacity_checks_against_exhaustive_subsets", "ten_survivor_subsets",
        "worst_sixth_factorial", "pure_error_cutoffs", "saturation_precision")}, indent=2))


if __name__ == "__main__":
    main()
