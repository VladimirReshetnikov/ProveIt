#!/usr/bin/env python3
"""Exhaustively check the restriction-monotonicity theorem for n <= 7.

The checks are finite evidence, not a replacement for the proof in the
accompanying research notes.  It is enough to inspect adjacent permutations
in the lexicographic list: a finite list is nondecreasing exactly when every
adjacent pair is nondecreasing.
"""

from itertools import permutations
import json
from pathlib import Path


def predicted_monotone(n, subset):
    return (
        len(subset) <= 1
        or len(subset) == n
        or (n == 3 and subset == frozenset((0, 2)))
    )


def check(maximum=7):
    report = []
    total_pairs = 0
    for n in range(maximum + 1):
        words = list(permutations(range(n)))
        monotone_subsets = []
        checked = 0
        witnesses = []
        for mask in range(1 << n):
            subset = frozenset(i for i in range(n) if (mask >> i) & 1)
            previous_word = words[0]
            previous_image = tuple(x for x in previous_word if x in subset)
            witness = None
            for word in words[1:]:
                image = tuple(x for x in word if x in subset)
                checked += 1
                if previous_image > image and witness is None:
                    witness = {
                        "subset": sorted(subset),
                        "lower": list(previous_word),
                        "upper": list(word),
                        "lower_restriction": list(previous_image),
                        "upper_restriction": list(image),
                    }
                previous_word, previous_image = word, image
            actual = witness is None
            assert actual == predicted_monotone(n, subset), (n, subset, witness)
            if actual:
                monotone_subsets.append(sorted(subset))
            else:
                witnesses.append(witness)
        total_pairs += checked
        report.append({
            "n": n,
            "permutations": len(words),
            "subsets": 1 << n,
            "adjacent_comparisons": checked,
            "monotone_subsets": monotone_subsets,
            "nonmonotone_subset_count": len(witnesses),
            "sample_violation": witnesses[0] if witnesses else None,
        })
    return {"maximum_n": maximum, "total_adjacent_comparisons": total_pairs,
            "all_predictions_agree": True, "results": report}


if __name__ == "__main__":
    result = check()
    target = Path(__file__).with_name("restriction_checks.json")
    target.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({
        "all_predictions_agree": result["all_predictions_agree"],
        "maximum_n": result["maximum_n"],
        "total_adjacent_comparisons": result["total_adjacent_comparisons"],
        "monotone_subset_counts": [len(row["monotone_subsets"]) for row in result["results"]],
        "report": str(target),
    }, indent=2))
