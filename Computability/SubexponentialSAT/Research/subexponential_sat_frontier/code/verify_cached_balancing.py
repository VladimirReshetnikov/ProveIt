#!/usr/bin/env python3
"""Compare entire exact certificates with the preserved incoming implementation."""
import argparse
import hashlib
import itertools
import json
import random
from pathlib import Path
import cached_balancing as improved
import reference_balanced_packing as reference


def run_checks():
    count = 0
    candidate_scores = 0
    rng = random.Random(20261027)
    cases = [[], [[]], [[], []], [[0]], [[3]], [[0, 0, 0]], [[4], [0], [7]]]
    for values in itertools.product(range(3), repeat=4):
        cases.append([list(values[:2]), list(values[2:])])
    for _ in range(80):
        n, m = rng.randrange(1, 9), rng.randrange(1, 12)
        cases.append([[rng.randrange(0, 5) if rng.random() < .4 else 0
                       for _ in range(m)] for _ in range(n)])
    for adjacency in cases:
        for labels in (1, 2, 3, 4, 7):
            old = reference.balance_pair_labels(adjacency, labels, keep_certificate=True)
            new = improved.balance_pair_labels(adjacency, labels, keep_certificate=True)
            if old != new:
                raise RuntimeError(f"Exact certificate mismatch: {adjacency}, Q={labels}")
            without = improved.balance_pair_labels(adjacency, labels, keep_certificate=False)
            expected = dict(old, steps=[])
            if without != expected:
                raise RuntimeError("Certificate-disabled mode changed the result")
            candidate_scores += sum(len(step["candidate_scores"]) for step in new["steps"])
            count += 1
    negatives = [([[1], []], 2, 8), ([[1, -1]], 2, 8), ([[True]], 2, 8),
                 ([[1]], 0, 8), ([[1]], 2, 1), ([[1]], 2.0, 8)]
    negative_checks = 0
    for adjacency, labels, smoothness in negatives:
        for implementation in (reference, improved):
            try:
                implementation.balance_pair_labels(adjacency, labels, smoothness)
            except ValueError:
                negative_checks += 1
            else:
                raise RuntimeError("A negative control was accepted")
    path = Path(reference.__file__)
    return {"status": "pass", "seed": 20261027, "complete_certificate_comparisons": count,
            "exact_candidate_scores_compared": candidate_scores,
            "certificate_disabled_comparisons": count,
            "rejected_negative_controls_across_both_implementations": negative_checks,
            "reference_file": path.name,
            "reference_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            "reference_source": "docs/incoming/eth_asymmetric_packet_balancing_2026-10-26.zip::eth_asymmetric_packet_balancing_2026-10-26/code/balanced_packing.py",
            "reference_repository_commit": "ab2fbc9e03d5c3d0ad6dec8686960bfe498b0b06"}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output")
    options = parser.parse_args()
    report = json.dumps(run_checks(), indent=2)+"\n"
    if options.output:
        Path(options.output).write_text(report)
    print(report)
