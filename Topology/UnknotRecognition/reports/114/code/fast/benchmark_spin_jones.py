"""Paired exact full-Jones queries: faithful Potts versus two-spin tensors.

Default-query arms include fresh Diagram construction and all ordering costs.
Matched-order arms use one certified crossing order prepared outside timing;
they include fresh Diagram construction, tensor/cochain setup and decoding.
Every completed arm returns the same full polynomial.  Censored queries are
retained and never converted to completed-query speedup ratios.
"""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import platform
import random
from statistics import median
import sys
from time import perf_counter

from fastunknot import Diagram
from fastunknot.faithful_jones import (faithful_colors, faithful_potts_exact,
                                      reconstruct_jones)
from fastunknot.filters import FilterLimit
from fastunknot.geometry import ScanLimit
from fastunknot.ordering import best_scan_order, order_profile
from fastunknot.potts_exact import potts_exact
from fastunknot.separator_order import width_bounded_scan_order
from fastunknot.spin_jones import spin_jones_exact
from check_potts_independent import laurent_jones
from separator_research.graphs import tree_medial

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT/'tests'))
from disk_grid import descending_grid, verify_descending


def matched_potts(diagram, **options):
    result = potts_exact(diagram, colors=faithful_colors(diagram.crossings), **options)
    polynomial = reconstruct_jones(result, check=options['check'])
    result['jones_polynomial'] = dict(variable='t', coefficients_hex=[
        [degree, hex(value)] for degree, value in polynomial.items()])
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--rounds', type=int, default=7)
    parser.add_argument('--seconds', type=float, default=3)
    parser.add_argument('--only', help='one named benchmark input, for a focused follow-up')
    args = parser.parse_args()
    if args.rounds < 1 or not 0 < args.seconds <= 60:
        parser.error('rounds must be positive and seconds must be in (0,60]')
    cases = []
    for name in ('trefoil', 'conway', 'kinoshita_terasaka', 'hard_unknot_8', 'stress_braid5_36'):
        diagram = Diagram.from_json(json.loads((ROOT/'examples'/(name+'.json')).read_text()))
        cases.append((name, diagram.pd, None))
    cases.append(('weaving-10', Diagram.from_braid(3, [1, -2]*5).pd, None))
    cases.append(('torus-101', Diagram.from_braid(2, [1]*101).pd, None))
    cases.extend((f'tree-{height}', tree_medial(height).pd, None) for height in (6, 7))
    cases.extend((f'grid-{size}', descending_grid(size), None) for size in (8, 10, 12, 14))
    shuffled = list(range(64))
    random.Random(26100859).shuffle(shuffled)
    cases.append(('grid-8-shuffled', descending_grid(8), shuffled))
    if args.only:
        cases = [case for case in cases if case[0] == args.only]
        if not cases:
            parser.error('unknown --only input')
    rng, rows = random.Random(26100860), []
    arms = ('potts', 'potts-control', 'spin', 'matched-potts', 'matched-spin')
    for name, pd, supplied_order in cases:
        original = Diagram.from_pd(pd)
        candidate = supplied_order
        if supplied_order is not None:
            greedy = best_scan_order(pd, tries=min(len(pd), 12))
            candidate = min((supplied_order, greedy), key=lambda order: order_profile(pd, order))
        certificate = width_bounded_scan_order(pd, order=candidate)
        matched_order = certificate['order']
        if original.crossings <= 12:
            oracle = {-degree: value for degree, value in laurent_jones(original).items()}
            oracle_kind = 'independent-whole-cube'
        elif name.startswith('grid-'):
            verify_descending(pd)
            oracle, oracle_kind = {0: 1}, 'verified-descending-diagram'
        else:
            oracle, oracle_kind = None, 'completed-arms-compared'
        samples = []
        polynomial_record = None
        for repetition in range(args.rounds+1):
            sequence = list(arms)
            rng.shuffle(sequence)
            elapsed, summary, results = {}, {}, {}
            for arm in sequence:
                start = perf_counter()

                def check():
                    if perf_counter()-start > args.seconds:
                        raise ScanLimit('per-query benchmark deadline')

                stats = {}
                try:
                    options = dict(check=check, statistics=stats,
                                   max_states=4096, max_transitions=200000)
                    diagram = Diagram.from_pd(pd)
                    if arm in ('potts', 'potts-control'):
                        result = faithful_potts_exact(diagram, order=supplied_order,
                                                      include_polynomial=True, **options)
                    elif arm == 'spin':
                        result = spin_jones_exact(diagram, order=supplied_order,
                                                   include_polynomial=True, **options)
                    elif arm == 'matched-potts':
                        result = matched_potts(diagram, order=matched_order, **options)
                    else:
                        result = spin_jones_exact(diagram, order=matched_order,
                            include_polynomial=True, certify_order=False, **options)
                except (FilterLimit, ScanLimit) as exc:
                    elapsed[arm] = perf_counter()-start
                    summary[arm] = dict(status='CAPPED', reason=str(exc),
                        transitions=getattr(exc, 'transitions', None),
                        peak_states=getattr(exc, 'peak_states', None),
                        ordering_policy=stats.get('ordering_policy'))
                    continue
                elapsed[arm] = perf_counter()-start
                results[arm] = result
                polynomial = {degree: int(value, 16) for degree, value in
                              result['jones_polynomial']['coefficients_hex']}
                if oracle is not None:
                    assert polynomial == oracle, (name, arm, polynomial, oracle)
                if polynomial_record is None:
                    polynomial_record = result['jones_polynomial']
                assert result['jones_polynomial'] == polynomial_record, (name, arm)
                summary[arm] = dict(status='COMPLETE', differs=result['differs'],
                    transitions=result['transitions'], peak_states=result['peak_states'],
                    coefficient_bits=result['max_coefficient_bits'],
                    boundary=result['max_boundary'], cochain_l1=result.get('cochain_l1'),
                    ordering_policy=result.get('ordering_policy'))
            if 'potts' in results and 'potts-control' in results:
                assert results['potts'] == results['potts-control']
            if repetition:
                samples.append(dict(order=sequence, seconds=elapsed, result=summary))
        complete = {arm: sum(sample['result'][arm]['status'] == 'COMPLETE' for sample in samples)
                    for arm in arms}
        medians = {arm: median(sample['seconds'][arm] for sample in samples) for arm in arms}
        paired = {}
        for left, right in (('potts', 'potts-control'), ('potts', 'spin'),
                            ('matched-potts', 'matched-spin')):
            if complete[left] == complete[right] == args.rounds:
                paired[left+'/'+right] = median(sample['seconds'][left]/sample['seconds'][right]
                                                for sample in samples)
        rows.append(dict(name=name, crossings=len(pd), pd=pd, supplied_order=supplied_order,
                         matched_order_certificate=certificate, oracle=oracle_kind,
                         polynomial=polynomial_record, complete_queries=complete,
                         median_seconds=medians, median_paired_ratios=paired, samples=samples))
        print(name, 'ms', {arm: round(1000*value, 3) for arm, value in medians.items()},
              'completed', complete, flush=True)
    files = ('fastunknot/spin_jones.py', 'fastunknot/faithful_jones.py',
             'fastunknot/potts_exact.py', 'fastunknot/adaptive_potts.py',
             'fastunknot/separator_order.py', 'benchmark_spin_jones.py',
             'tests/test_spin_jones.py')
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(dict(
        scope='identical full-polynomial queries; default and separately matched-order scopes',
        python=sys.version, platform=platform.platform(), seed=26100860,
        rounds=args.rounds, excluded_warmups=1, max_states=4096,
        max_transitions=200000, seconds_per_query=args.seconds,
        baseline_commit='8a95834940cf77cdab1b39571ffc102ca8b6bede',
        source_sha256={name: sha256((ROOT/name).read_bytes()).hexdigest() for name in files},
        rows=rows), indent=2)+'\n')


if __name__ == '__main__':
    main()
