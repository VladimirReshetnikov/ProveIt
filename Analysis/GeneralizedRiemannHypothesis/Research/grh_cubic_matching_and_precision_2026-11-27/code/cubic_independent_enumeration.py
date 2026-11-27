#!/usr/bin/env python3
"""Independent exact finite check using local multiplicity triples, not Fourier sums.

Requires NumPy. Run from any directory; writes results/cubic_independent_enumeration.json relative to this package root.
"""
from itertools import product, combinations_with_replacement
from pathlib import Path
import json
import numpy as np


def main():
    cases = ([(1, k) for k in range(1, 7)]
             + [(2, k) for k in range(1, 6)]
             + [(3, k) for k in range(1, 3)])
    out = []
    for r, k in cases:
        vectors = np.array(list(product(range(3), repeat=r)), dtype=np.int16)
        n = len(vectors)
        evaluations = (vectors @ vectors.T) % 3
        packets = list(combinations_with_replacement(range(n), k))
        signatures = np.empty((len(packets), n), dtype=np.int16)
        for i, packet in enumerate(packets):
            values = evaluations[list(packet), :]
            # k fixed: the first two multiplicities uniquely determine the third.
            signatures[i] = ((values == 0).sum(axis=0)
                             + (k + 1) * (values == 1).sum(axis=0))
        minimum, count, sample = n + 1, 0, None
        for i in range(len(packets) - 1):
            distances = (signatures[i + 1:] != signatures[i]).sum(axis=1)
            current = int(distances.min())
            if current < minimum:
                minimum = current
                count = int((distances == current).sum())
                sample = (packets[i], packets[i + 1 + int(np.argmin(distances))])
            elif current == minimum:
                count += int((distances == current).sum())
        a = 0
        while 3 ** (a + 1) <= k:
            a += 1
        predicted = (2 if k >= 3 ** (r - 1) else
                     2 * 3 ** (r - a - 1) if k < 2 * 3 ** a else
                     4 * 3 ** (r - a - 2))
        assert minimum == predicted, (r, k, minimum, predicted)
        out.append({
            "rank": r, "packet_size": k, "packets": len(packets),
            "unordered_distinct_pairs": len(packets) * (len(packets) - 1) // 2,
            "minimum_disagreement_classes": minimum, "classes": n,
            "minimizing_pairs": count, "sample": [list(x) for x in sample],
        })
    destination = Path(__file__).resolve().parent.parent / "results" / "cubic_independent_enumeration.json"
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(out, indent=2) + "\n")
    print(json.dumps({"cases": len(out), "unordered_distinct_pairs":
                      sum(row["unordered_distinct_pairs"] for row in out),
                      "all_checks_passed": True}, indent=2))


if __name__ == "__main__":
    main()
