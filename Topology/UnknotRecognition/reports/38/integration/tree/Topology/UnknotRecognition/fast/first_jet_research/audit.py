"""Audit eligible pre-cancellation blocks in actual production knot scans."""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import random
import sys
from time import monotonic, perf_counter


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--fast-root', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--knots', type=int, default=180)
    args = parser.parse_args()
    sys.path.insert(0, str(args.fast_root))
    from fastunknot import Diagram
    from fastunknot.component_scan import components
    from fastunknot.first_jet import first_jet_profile, FirstJetBudget
    from fastunknot.geometry import ScanLimit
    from fastunknot.ordering import best_scan_order
    from fastunknot.scan_fast import FastScan

    counts, examples = Counter(), []

    class Probe(FastScan):
        def eliminate(self):
            counts['stages'] += 1
            before = []
            for group in components(self):
                counts['pre_components'] += 1
                if len({self.mid[v] for v in group}) != 1:
                    counts['mixed_matching_components'] += 1
                    continue
                if not self.points:
                    continue
                data = first_jet_profile(self, group, max_work=250000, audit=True)
                if data is None:
                    continue
                before.append((group, data))
                counts['eligible_components'] += 1
                counts['eligible_objects'] += len(group)
                counts['nonsingleton_components'] += len(group) > 1
                counts['components_with_scalar_units'] += data['scalar_rank'] > 0
                counts['scalar_pairs'] += data['scalar_rank']
                counts['residual_objects'] += data['t']
                counts['kappa_zero'] += data['kappa'] == 0
                counts['kappa_one'] += data['kappa'] == 1
                counts['kappa_large'] += data['kappa'] >= 2
                counts['t_exceeds_kappa'] += data['t'] > data['kappa']
                counts['query_work_units'] += data['work_units']
                if len(examples) < 12 and len(group) > 1:
                    examples.append({k: data[k] for k in
                                     ('objects', 'scalar_rank', 't', 'kappa', 'kind')})
            super().eliminate()
            for group, data in before:
                survivors = [v for v in group if self.mid[v] is not None]
                if len(survivors) != data['t']:
                    raise AssertionError('pre-query disagrees with scalar elimination')
                if survivors:
                    after = first_jet_profile(self, survivors, max_work=250000, audit=True)
                    if after['kappa'] != data['kappa']:
                        raise AssertionError('first jet changed under scalar elimination')
                counts['pre_post_checks'] += 1
            for a, row in enumerate(self.out):
                if row is None:
                    continue
                for b, value in row.items():
                    if self.mid[a] == self.mid[b]:
                        counts['minimal_endomorphism_entries'] += 1
                        sigma = 0
                        for j in range(len(self.algebra.pairs[self.mid[a]])):
                            sigma ^= (value >> (1 << j)) & 1
                        counts['odd_minimal_endomorphism_entries'] += sigma

    rng = random.Random(29002)
    records = []
    accepted = 0
    attempts = 0
    started = perf_counter()
    while accepted < args.knots:
        attempts += 1
        strands = rng.randrange(2, 6)
        word = [rng.choice((-1, 1)) * rng.randrange(1, strands)
                for _ in range(rng.randrange(1, 15))]
        try:
            diagram = Diagram.from_braid(strands, word)
        except ValueError:
            continue
        accepted += 1
        shuffled = list(range(diagram.crossings))
        rng.shuffle(shuffled)
        for label, order in [('greedy', best_scan_order(diagram.pd)),
                             ('shuffled', shuffled)]:
            scan = Probe(max_objects=10000, deadline=monotonic() + 3)
            entry = dict(strands=strands, word=word, order=order, ordering=label)
            try:
                for index in order:
                    scan.add_crossing(diagram.pd[index])
                scan.check_d_squared()
                entry['rank'] = scan.total_rank()
                entry['status'] = 'complete'
                counts['completed_scans'] += 1
            except (ScanLimit, FirstJetBudget) as error:
                entry['status'] = type(error).__name__
                counts['limited_scans'] += 1
            records.append(entry)
    result = dict(seed=29002, attempts=attempts, knots=accepted,
                  counts=dict(counts), examples=examples, records=records,
                  elapsed_seconds=perf_counter() - started,
                  scope='Read-only pre-Schur eligibility and rank invariance, not a speedup benchmark.',
                  source_sha256={name: hashlib.sha256((args.fast_root / 'fastunknot' / name).read_bytes()).hexdigest()
                                 for name in ('first_jet.py', 'scan_fast.py', 'component_scan.py')})
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'records'}, indent=2))


if __name__ == '__main__':
    main()
