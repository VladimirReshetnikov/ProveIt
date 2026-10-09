"""Paired Jones kernels and normal recognition; no inferred detection equivalence.

Kernels share a supplied order, excluding its construction. The two exact
arms use q=6 and must agree. Matching and modular q=5 use different scalar
specializations and can differ in obstruction power. Pipeline timings include
Diagram construction, ordering, all default certificates and fallbacks.
"""
import argparse
import json
from pathlib import Path
import platform
import random
import statistics
from time import perf_counter

from fastunknot import Diagram, recognize
from fastunknot.filters import jones_obstruction
from fastunknot.ordering import best_scan_order
from fastunknot.potts import potts_obstruction
from fastunknot.potts_exact import potts_exact
from fastunknot.potts_factorized_exact import factorized_potts_exact


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    cases = [("weaving10", {"braid": {"strands": 3, "word": [1, -2] * 5}}, None),
             ("weaving98", {"braid": {"strands": 3, "word": [1, -2] * 49}}, None),
             ("fragmented16", {"braid": {"strands": 5, "word":
              [-2, -3, 4, -4, 4, -4, -3, 2, -4, 1, 3, 4, 1, 1, 2, 3]}},
              [6, 12, 15, 0, 2, 10, 8, 4, 3, 5, 11, 13, 7, 14, 1, 9])]
    for name in ("conway", "kinoshita_terasaka", "stress_braid5_36", "hard_unknot_8"):
        cases.append((name, json.loads((Path(__file__).parent / "examples" / (name + ".json")).read_text()), None))
    rng = random.Random(2026100817)
    rows = []
    for name, source, supplied in cases:
        diagram = Diagram.from_json(source)
        order = supplied if supplied is not None else best_scan_order(diagram.pd, tries=min(diagram.crossings, 12))
        options = dict(order=order, max_states=None, max_transitions=None)
        arms = dict(exact=lambda: potts_exact(diagram, **options),
                    control=lambda: potts_exact(diagram, **options),
                    factored=lambda: factorized_potts_exact(diagram, **options),
                    matching=lambda: jones_obstruction(diagram, **options),
                    potts5=lambda: potts_obstruction(diagram, **options))
        pipeline = {backend: (lambda backend=backend: recognize(
            Diagram.from_json(source), jones_backend=backend, seconds=10).to_json())
            for backend in ("matching", "potts-exact", "potts-exact-factorized")}
        samples = []
        for _ in range(7):
            shuffled = list(arms); rng.shuffle(shuffled)
            times, results = {}, {}
            for arm in shuffled:
                start = perf_counter(); results[arm] = arms[arm]()
                times[arm] = perf_counter() - start
            for field in ("partition_function", "unknot_partition", "differs"):
                assert results["exact"][field] == results["factored"][field]
                assert results["exact"][field] == results["control"][field]
            pipeline_order = list(pipeline); rng.shuffle(pipeline_order)
            pipeline_times, pipeline_results = {}, {}
            for arm in pipeline_order:
                start = perf_counter(); pipeline_results[arm] = pipeline[arm]()
                pipeline_times[arm] = perf_counter() - start
            assert len({r["status"] for r in pipeline_results.values()}) == 1
            samples.append(dict(order=shuffled, seconds=times, pipeline_order=pipeline_order,
                                pipeline_seconds=pipeline_times, pipeline_results=pipeline_results))
        row = dict(name=name, source=source, supplied_order=order, results=results, samples=samples,
                   median_exact_over={arm: statistics.median(s["seconds"]["exact"] / s["seconds"][arm]
                                      for s in samples) for arm in arms if arm != "exact"},
                   median_pipeline_matching_over={arm: statistics.median(
                       s["pipeline_seconds"]["matching"] / s["pipeline_seconds"][arm]
                       for s in samples) for arm in pipeline if arm != "matching"})
        rows.append(row)
        print(name, row["median_exact_over"], row["median_pipeline_matching_over"], flush=True)
    args.output.write_text(json.dumps(dict(python=platform.python_version(), seed=2026100817,
                                          rounds=7, scope=__doc__, cases=rows), indent=2) + "\n")


if __name__ == "__main__":
    main()
