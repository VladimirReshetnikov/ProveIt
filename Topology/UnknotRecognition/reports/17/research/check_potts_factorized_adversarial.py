"""Supplemental direct-labelled-spin tests of zero component tensors."""
from itertools import product
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
FAST = ROOT / "fast" if (ROOT / "fast").is_dir() else ROOT / "work" / "fast"
sys.path.insert(0, str(FAST))
from fastunknot.filters import PRIME
from fastunknot.potts_factorized import factorized_partition


def main():
    count = 0
    for colors in range(1, 7):
        graphs = [
            (3, [(0, 1, 0), (1, 2, 1)]),
            (5, [(0, 1, 0), (2, 3, 1), (1, 2, 1), (3, 4, 0)]),
            (4, [(0, 1, 0), (1, 1, 1), (1, 2, 1), (2, 3, 0), (0, 3, 1)]),
        ]
        for vertices, edges in graphs:
            for wa in (0, 1 - colors, -1, PRIME - 1):
                for wb in (0, 1, -1):
                    weights = {0: wa, 1: wb}
                    for order in (list(range(len(edges))), list(reversed(range(len(edges))))):
                        expected = 0
                        for spins in product(range(colors), repeat=vertices):
                            term = 1
                            for u, v, e in edges:
                                if spins[u] == spins[v]:
                                    term = term * weights[e] % PRIME
                            expected += term
                        got = factorized_partition(vertices, edges, order, colors=colors,
                                                   equal_weights=weights, max_states=None,
                                                   max_transitions=None)
                        assert got["partition_function"] == expected % PRIME
                        count += 1
    try:
        factorized_partition(2, [(0, 1, 0)], [0], colors=2, equal_weights={0: .5})
    except (ValueError, TypeError):
        pass
    else:
        raise AssertionError("noninteger weights were accepted by the exact modular kernel")
    result = {"status": "PASS", "direct_labeled_spin_comparisons": count,
              "noninteger_weight_rejections": 1,
              "scope": "Zero, negative and cancellation-forcing weights; no timing claim"}
    Path(__file__).with_name("potts_factorized_adversarial.json").write_text(
        json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
