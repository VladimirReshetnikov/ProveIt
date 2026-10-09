"""Adaptive faithful Jones versus completed Potts and spin full-polynomial queries.

Fresh PD validation, ordering, scalar work and decoding are timed together.
The Potts A/A control and shared local caps expose both overhead and capacity.
"""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import platform
import random
from statistics import median
import subprocess
import sys
from time import perf_counter

from benchmark_whitehead_power import historical
from check_potts_independent import laurent_jones
from fastunknot import Diagram
from fastunknot.adaptive_jones import adaptive_jones_exact
from fastunknot.filters import FilterLimit
from fastunknot.geometry import ScanLimit
from fastunknot.spin_jones import spin_jones_exact
from separator_research.graphs import tree_medial

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT/'tests'))
from disk_grid import descending_grid, verify_descending

BASELINE = '153bc2362700d5d88e534ba269fdd03d9b84deb0'
FILES = ('fastunknot/adaptive_jones.py', 'fastunknot/spin_jones.py', 'fastunknot/faithful_jones.py',
         'fastunknot/potts_exact.py', 'fastunknot/adaptive_potts.py',
         'fastunknot/separator_order.py', 'benchmark_adaptive_jones.py',
         'tests/test_adaptive_jones.py')


def source_hashes():
    return {name: sha256((ROOT/name).read_bytes()).hexdigest() for name in FILES}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    hashes = source_hashes()
    old = historical('faithful_jones', BASELINE).faithful_potts_exact
    cases = []
    for name in ('trefoil', 'conway', 'kinoshita_terasaka', 'hard_unknot_8', 'stress_braid5_36'):
        pd = Diagram.from_json(json.loads((ROOT/'examples'/(name+'.json')).read_text())).pd
        cases.append((name, pd, None))
    cases.append(('weaving-10', Diagram.from_braid(3, [1, -2]*5).pd, None))
    cases.append(('torus-101', Diagram.from_braid(2, [1]*101).pd, None))
    cases.extend((f'tree-{h}', tree_medial(h).pd, None) for h in (6, 7))
    cases.extend((f'grid-{n}', descending_grid(n), None) for n in (8, 10, 12, 14))
    supplied = list(range(64))
    random.Random(26100859).shuffle(supplied)
    cases.append(('grid-8-shuffled', descending_grid(8), supplied))
    rng, rows = random.Random(26100867), []
    arms = ('baseline', 'control', 'spin', 'adaptive')
    for name, pd, order in cases:
        if len(pd) <= 12:
            expected = {-k: c for k, c in laurent_jones(Diagram.from_pd(pd)).items()}
            oracle = 'independent-whole-cube'
        elif name.startswith('grid-'):
            verify_descending(pd)
            expected, oracle = {0: 1}, 'verified-descending'
        else:
            expected, oracle = None, 'completed-arms-agree'
        samples = []
        for repetition in range(6):
            sequence, measurements, results = list(arms), {}, {}
            rng.shuffle(sequence)
            for arm in sequence:
                start = perf_counter()

                def check():
                    if perf_counter()-start > 3:
                        raise ScanLimit('three-second full-Jones query allowance')

                try:
                    diagram = Diagram.from_pd(pd)
                    options = dict(order=order, check=check, include_polynomial=True,
                                   max_states=4096, max_transitions=200000)
                    if arm in ('baseline', 'control'):
                        result = old(diagram, **options)
                    elif arm == 'spin':
                        result = spin_jones_exact(diagram, **options)
                    else:
                        result = adaptive_jones_exact(diagram, **options)
                except (FilterLimit, ScanLimit) as exc:
                    measurements[arm] = dict(status='LIMIT', seconds=perf_counter()-start,
                        reason=str(exc), transitions=getattr(exc, 'transitions', None),
                        peak_states=getattr(exc, 'peak_states', None))
                    continue
                elapsed = perf_counter()-start
                results[arm] = result
                polynomial = {k: int(c, 16) for k, c in
                              result['jones_polynomial']['coefficients_hex']}
                if expected is None:
                    expected = polynomial
                assert polynomial == expected, (name, arm)
                record = dict(status='COMPLETE', seconds=elapsed,
                    polynomial_sha256=sha256(json.dumps(result['jones_polynomial'],
                                                       sort_keys=True).encode()).hexdigest())
                for key in ('peak_states', 'transitions', 'max_boundary', 'max_coefficient_bits',
                            'max_frontier_mantissa_bits', 'max_frontier_valuation'):
                    record[key] = result.get(key)
                record['backend_policy'] = result.get('backend_policy')
                measurements[arm] = record
            if 'baseline' in results and 'control' in results:
                assert results['baseline'] == results['control']
            if 'adaptive' in results:
                policy = results['adaptive']['backend_policy']
                assert results['adaptive']['transitions'] == policy['spent_transitions']
                assert policy['spent_transitions'] == policy['potts_transitions']+policy['spin_transitions']
            if repetition:
                samples.append(dict(order=sequence, measurements=measurements))
        medians = {arm: median(s['measurements'][arm]['seconds'] for s in samples) for arm in arms}
        counts = {arm: sum(s['measurements'][arm]['status'] == 'COMPLETE' for s in samples)
                  for arm in arms}
        ratios = {}
        for left, right in [('baseline', 'control'), ('baseline', 'adaptive'),
                            ('spin', 'adaptive')]:
            if counts[left] == counts[right] == 5:
                ratios[left+'/'+right] = median(s['measurements'][left]['seconds']/
                    s['measurements'][right]['seconds'] for s in samples)
        rows.append(dict(name=name, pd=pd, supplied_order=order, oracle=oracle,
            samples=samples, median_seconds=medians, completed=counts, median_paired_ratios=ratios))
        print(name, {a: round(1000*v, 3) for a, v in medians.items()}, counts, flush=True)
    assert hashes == source_hashes(), 'source changed during benchmark'
    args.output.write_text(json.dumps(dict(python=sys.version, platform=platform.platform(),
        baseline_commit=BASELINE, seed=26100867, rounds=5, excluded_warmups=1,
        source_sha256=hashes, source_hashes_unchanged=True,
        archived_faithful_sha256=sha256(subprocess.check_output(['git', 'show',
            BASELINE+':Topology/UnknotRecognition/fast/fastunknot/faithful_jones.py'])).hexdigest(),
        seconds=3, max_states=4096, max_transitions=200000,
        scope='Full polynomial with fresh PD, ordering, turning, contraction and decoding',
        censoring='Limits are incomplete queries, never completed-time denominators',
        rows=rows), indent=2)+'\n')


if __name__ == '__main__':
    main()
