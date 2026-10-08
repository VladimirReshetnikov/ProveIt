"""Recover and check the erased quantum shifts of the production scanner.

The recurrence is from the incoming dense-algebra report. This is a diagnostic
subclass, not state added to normal recognition. It checks the live upstream
implementation before and after cancellation, with optional component algebra.
"""
import argparse
import json
from pathlib import Path
import random

from fastunknot import Diagram
from fastunknot.component_algebra import install_on_empty_scan
from fastunknot.diagram import DiagramError
from fastunknot.frobenius.subset import support
from fastunknot.ordering import best_scan_order
from fastunknot.scan_fast import FastScan


class GradingAuditScan(FastScan):
    def __init__(self, **options):
        super().__init__(**options)
        self.qshift = [0]
        self.checked_entries = self.checked_terms = self.max_dot_degree = 0

    def add_crossing(self, slots, reduce_now=True):
        old_mid, old_q = self.mid, self.qshift
        super().add_crossing(slots, reduce_now=False)
        shifts = []
        for a, matching in enumerate(old_mid):
            if matching is None:
                continue
            for smoothing in (0, 1):
                closed = self.algebra.glue(matching, smoothing)[1]
                shifts.extend(old_q[a] + smoothing + closed - 2 * label.bit_count()
                              for label in range(1 << closed))
        if len(shifts) != len(self.mid):
            raise ArithmeticError("delooping order and recovered shifts disagree")
        self.qshift = shifts
        self.check_grading()
        if reduce_now:
            self.eliminate()
            self.check_grading()

    def check_grading(self):
        half_width = len(self.points) // 2
        for a, row in enumerate(self.out):
            if not row:
                continue
            for b, value in row.items():
                circles = self.algebra.basis(self.mid[a], self.mid[b])[1]
                expected = circles - half_width + self.qshift[b] - self.qshift[a]
                self.checked_entries += 1
                for monomial in support(value):
                    degree = monomial.bit_count()
                    if 2 * degree != expected:
                        raise ArithmeticError(f"lost quantum grading on {a}->{b}: {2*degree} != {expected}")
                    self.checked_terms += 1
                    self.max_dot_degree = max(self.max_dot_degree, degree)
                if self.mid[a] == self.mid[b] and value & 1 and value != 1:
                    raise ArithmeticError("a genuine homogeneous unit must be the identity")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--random", type=int, default=80)
    args = parser.parse_args()
    rng = random.Random(2026100801)
    examples = Path(__file__).parent / "examples"
    cases = [(name, Diagram.from_json(json.loads((examples / (name + '.json')).read_text())))
             for name in ('trefoil', 'figure_eight', 'hard_unknot_8', 'conway',
                          'kinoshita_terasaka', 'torus_3_5', 'unknot_braid40')]
    accepted = 0
    while accepted < args.random:
        strands = rng.randrange(2, 6)
        word = [rng.choice((-1, 1))*rng.randrange(1, strands) for _ in range(rng.randrange(1, 13))]
        try:
            diagram = Diagram.from_braid(strands, word)
        except DiagramError:
            continue
        cases.append((f"random_{accepted}", diagram))
        accepted += 1
    rows = []
    for name, diagram in cases:
        orders = [list(range(diagram.crossings)), best_scan_order(diagram.pd)]
        if diagram.crossings <= 12:
            shuffled = list(range(diagram.crossings))
            rng.shuffle(shuffled)
            orders.append(shuffled)
        for order in orders:
            expected = None
            for mode in ('standard', 'component-dense'):
                scan = GradingAuditScan(max_objects=50000, shape_cache=False)
                if mode != 'standard':
                    install_on_empty_scan(scan, minimum_pairs=0, method='fast')
                for crossing in order:
                    scan.add_crossing(diagram.pd[crossing])
                    scan.check_d_squared()
                rank = scan.total_rank()
                by_degree = scan.ranks_by_degree()
                if expected is not None and by_degree != expected:
                    raise ArithmeticError("dense composition changed homology")
                expected = by_degree
                rows.append(dict(name=name, pd=diagram.pd, order=order, mode=mode, rank=rank,
                    by_degree=by_degree, entries=scan.checked_entries, terms=scan.checked_terms,
                    max_dot_degree=scan.max_dot_degree))
    result = dict(status='passed', seed=2026100801, cases=len(cases), scans=len(rows),
                  entries=sum(r['entries'] for r in rows), terms=sum(r['terms'] for r in rows),
                  max_dot_degree=max(r['max_dot_degree'] for r in rows), data=rows)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'data'}, indent=2))


if __name__ == '__main__':
    main()

