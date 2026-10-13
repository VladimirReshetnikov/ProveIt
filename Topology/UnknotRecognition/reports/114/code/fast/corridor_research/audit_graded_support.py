"""Measure the additional coverage of quantum support on actual scan stages.

All stages use ordinary sparse cancellation. Both shortcut tests are evaluated
on the same unreduced input, and the predicted full profile is checked against
the live objects after cancellation. This is a coverage audit, not a timing
benchmark, and failed support certificates are not recognition verdicts.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import sys
FAST = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(FAST))
import random

from fastunknot import Diagram
from fastunknot.diagram import DiagramError
from fastunknot.graded import GradedScan, graded_survivor_profile, support_has_no_differential
from fastunknot.ordering import best_scan_order
from fastunknot.scan_fast import FastScan


class SupportAuditScan(GradedScan):
    def __init__(self, **options):
        super().__init__(**options)
        self.stages = []

    def eliminate(self):
        self.check_grading()
        profile = graded_survivor_profile(self)
        degrees = {h for _, h, _ in profile}
        gap = not self.points or all(h + 1 not in degrees for h in degrees)
        graded = support_has_no_differential(self, profile)
        before = self.stats["schur_update_pairs"]
        FastScan.eliminate(self)
        observed = dict(Counter((matching, self.deg[a], self.qshift[a])
                               for a, matching in enumerate(self.mid) if matching is not None))
        if observed != profile:
            raise ArithmeticError("graded profile changed during scalar cancellation")
        self.check_grading()
        self.check_d_squared()
        self.stages.append(dict(boundary=len(self.points), survivors=self.live,
                                degree_gap=gap, graded_support=graded,
                                schur_updates=self.stats["schur_update_pairs"] - before))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--random", type=int, default=60)
    args = parser.parse_args()
    rng = random.Random(20261008)
    directory = FAST / "examples"
    names = ("conway", "figure_eight", "hard_unknot_8", "kinoshita_terasaka",
             "torus_3_5", "trefoil", "unknot", "unknot_braid40")
    cases = [(name, Diagram.from_json(json.loads((directory / (name + ".json")).read_text())))
             for name in names]
    cases.extend([("braid2_51", Diagram.from_braid(2, [1] * 51)),
                  ("torus3_10", Diagram.from_braid(3, [1, 2] * 10)),
                  ("alt3_4", Diagram.from_braid(3, [1, -2] * 4)),
                  ("morton", Diagram.from_braid(4, [-3, -3, 2, -3, 2, 1, 1, 1, -2, 1, -2]))])
    for i in range(args.random):
        while True:
            try:
                strands = rng.randrange(2, 6)
                word = [rng.choice((-1, 1)) * rng.randrange(1, strands)
                        for _ in range(rng.randrange(1, 15))]
                diagram = Diagram.from_braid(strands, word)
                break
            except DiagramError:
                pass
        cases.append((f"random{i}", diagram))
    rows = []
    for name, diagram in cases:
        order = best_scan_order(diagram.pd)
        scan = SupportAuditScan(max_objects=30000, shape_cache=False)
        for crossing in order:
            scan.add_crossing(diagram.pd[crossing])
        rows.append(dict(name=name, pd=diagram.pd, order=order,
                         rank=scan.total_rank(), stages=scan.stages))
    stages = [stage for row in rows for stage in row["stages"]]
    result = dict(seed=20261008, diagrams=len(rows), stages=len(stages),
                  degree_gap_shortcuts=sum(s["degree_gap"] for s in stages),
                  graded_support_shortcuts=sum(s["graded_support"] for s in stages),
                  additional_shortcuts=sum(s["graded_support"] and not s["degree_gap"] for s in stages),
                  total_schur_updates=sum(s["schur_updates"] for s in stages), data=rows)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k != "data"}, indent=2))


if __name__ == "__main__":
    main()
