"""Exhaustive pointed-scanner checks against the independent dense cube oracle.

Run python tools/verify_reduced_scan.py from the package root.  Defaults are
resolved relative to this script, so any working directory is supported.
This test intentionally imports the existing independent oracle,
which uses sets of labelled resolutions and F2 column reduction, not Planar.
"""
import importlib.util
import argparse
from itertools import product
import json
from pathlib import Path
import random
import sys
import time

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--fast-root", type=Path, default=Path(__file__).resolve().parents[1] / "fast")
    parser.add_argument("--output", type=Path, default=Path(__file__).resolve().parents[1] / "data/reduced_validation.json")
    options = parser.parse_args()
    fast_root = options.fast_root.resolve()
    sys.path.insert(0, str(fast_root))
    from fastunknot import Diagram, DiagramError, khovanov_rank
    from fastunknot.reduced_scan import reduced_khovanov_rank, reduced_khovanov_decision
    oracle_path = fast_root / "tests/test_fastunknot.py"
    spec = importlib.util.spec_from_file_location("dense_oracle", oracle_path)
    oracle = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(oracle)
    rng = random.Random(20261007)
    counts = {"dense_diagrams": 0, "scans": 0, "decision_scans": 0, "all_edge_order_scans": 0,
              "shape_cache_pairs": 0}
    started = time.perf_counter()
    for strands, lengths in ((2, (1, 3, 5)), (3, (2, 4, 6))):
        alphabet = tuple(x for i in range(1, strands) for x in (-i, i))
        for length in lengths:
            n = 0
            for word in product(alphabet, repeat=length):
                try:
                    d = Diagram.from_braid(strands, word)
                except DiagramError:
                    continue
                expected = oracle.reference_reduced_rank(d)
                counts["dense_diagrams"] += 1
                n += 1
                r = reduced_khovanov_rank(d.pd, check_d_squared=True)
                counts["scans"] += 1
                assert r["rank"] == expected, (word, r, expected)
                decision = reduced_khovanov_decision(d.pd, check_d_squared=True)
                counts["decision_scans"] += 1
                assert decision["status"] == ("UNKNOT" if expected == 1 else "KNOTTED"), word
                assert decision["lower_bound"] <= expected, word
                if length <= 4 or strands == 2:
                    orders = [list(range(length)), list(reversed(range(length))),
                              rng.sample(range(length), length)]
                    for edge in range(2 * length):
                        for order in orders:
                            rr = reduced_khovanov_rank(d.pd, order=order, edge=edge,
                                                       check_d_squared=True)
                            counts["scans"] += 1
                            counts["all_edge_order_scans"] += 1
                            assert rr["rank"] == expected, (word, order, edge, rr, expected)
                            assert rr["by_degree"] == r["by_degree"], (word, order, edge)
                elif n <= 32:
                    rr = reduced_khovanov_rank(d.pd, shape_cache=True,
                                               check_d_squared=True)
                    counts["scans"] += 1
                    counts["shape_cache_pairs"] += 1
                    assert rr["by_degree"] == r["by_degree"]
            print(strands, length, n, counts, flush=True)
    for name in ("trefoil", "figure_eight", "conway", "kinoshita_terasaka", "torus_3_5",
                 "hard_unknot_8", "unknot_braid40", "stress_braid5_36",
                 "grid_determinant_one_knot", "grid_scrambled_unknot"):
        d = Diagram.from_json(json.loads((fast_root / "examples" / (name + ".json")).read_text()))
        b = khovanov_rank(d.pd)
        for cache in (False, True):
            r = reduced_khovanov_rank(d.pd, order=b["order"], shape_cache=cache,
                                      check_d_squared=True)
            counts["scans"] += 1
            assert r["by_degree"] == {h: value // 2 for h, value in b["by_degree"].items()}, name
        counts["shape_cache_pairs"] += 1
    counts["elapsed_seconds"] = time.perf_counter() - started
    counts["status"] = "passed"
    options.output.parent.mkdir(parents=True, exist_ok=True)
    options.output.write_text(json.dumps(counts, indent=2) + "\n")
    print(json.dumps(counts, indent=2), flush=True)


if __name__ == "__main__":
    main()
