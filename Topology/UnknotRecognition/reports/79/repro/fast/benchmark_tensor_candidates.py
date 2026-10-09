"""Compare delivered tensor arithmetic on one common certified crossing order.

The candidate module is loaded byte-for-byte from the user-supplied research
archive. It is not installed as a production backend. All arms request full
Jones polynomials; order preparation is excluded and tensor preparation is
included. Timings include fresh PD validation and normalization/decoding.
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
from types import ModuleType
from zipfile import ZipFile

from fastunknot import Diagram
from fastunknot.filters import FilterLimit
from fastunknot.geometry import ScanLimit
from fastunknot.separator_order import width_bounded_scan_order
from fastunknot.spin_jones import spin_jones_exact
from separator_research.graphs import tree_medial
from check_potts_independent import laurent_jones

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT/'tests'))
from disk_grid import descending_grid, verify_descending

MEMBER = ('unknot_certified_primitives_20261008/integration/tree/'
          'Topology/UnknotRecognition/fast/fastunknot/tensor_jones.py')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--archive', type=Path, default=ROOT.parents[2]/
                        'docs/incoming/unknot_certified_primitives_20261008.zip')
    args = parser.parse_args()
    with ZipFile(args.archive) as archive:
        source = archive.read(MEMBER)
    candidate = ModuleType('fastunknot._research_tensor_candidate')
    candidate.__package__ = 'fastunknot'
    exec(compile(source, MEMBER, 'exec'), candidate.__dict__)
    cases = [('weaving-10', Diagram.from_braid(3, [1, -2]*5).pd),
             ('tree-7', tree_medial(7).pd),
             ('grid-12', descending_grid(12)), ('grid-14', descending_grid(14))]
    arms = ['spin', 'spin-control', 'valuation', 'global-shift']
    rng, rows = random.Random(26100862), []
    for name, pd in cases:
        certificate = width_bounded_scan_order(pd)
        order = certificate['order']
        if name.startswith('grid-'):
            verify_descending(pd)
            expected, oracle = {0: 1}, 'verified-descending'
        elif len(pd) <= 12:
            expected = {-d: c for d, c in laurent_jones(Diagram.from_pd(pd)).items()}
            oracle = 'independent-whole-cube'
        else:
            expected, oracle = None, 'completed-arms-agree'
        samples = []
        for repetition in range(6):
            sequence, measurements = list(arms), {}
            rng.shuffle(sequence)
            for arm in sequence:
                start = perf_counter()

                def check():
                    if perf_counter()-start > 3:
                        raise ScanLimit('three-second candidate benchmark deadline')

                try:
                    diagram = Diagram.from_pd(pd)
                    options = dict(order=order, check=check, max_states=4096,
                                   max_transitions=200000)
                    if arm.startswith('spin'):
                        result = spin_jones_exact(diagram, certify_order=False,
                                                  include_polynomial=True, **options)
                    else:
                        result = candidate.tensor_jones(diagram, certified=False,
                            arithmetic='integer' if arm == 'valuation' else 'integer-global',
                            **options)
                except (FilterLimit, ScanLimit) as exc:
                    measurements[arm] = dict(status='LIMIT', seconds=perf_counter()-start,
                        reason=str(exc))
                    continue
                elapsed = perf_counter()-start
                polynomial = {degree: int(value, 16) for degree, value in
                              result['jones_polynomial']['coefficients_hex']}
                if expected is None:
                    expected = polynomial
                assert polynomial == expected, (name, arm)
                measurements[arm] = dict(status='COMPLETE', seconds=elapsed,
                    peak_states=result['peak_states'], transitions=result['transitions'],
                    max_coefficient_bits=result['max_coefficient_bits'],
                    max_boundary=result['max_boundary'],
                    integer_encoding=result.get('integer_encoding'),
                    polynomial_sha256=sha256(json.dumps(result['jones_polynomial'],
                                            sort_keys=True).encode()).hexdigest())
            if repetition:
                samples.append(dict(order=sequence, measurements=measurements))
        medians = {arm: median(s['measurements'][arm]['seconds'] for s in samples)
                   for arm in arms}
        ratios = {}
        for left, right in [('spin', 'spin-control'), ('spin', 'valuation'),
                            ('global-shift', 'valuation')]:
            if all(s['measurements'][a]['status'] == 'COMPLETE'
                   for s in samples for a in (left, right)):
                ratios[left+'/'+right] = median(s['measurements'][left]['seconds']/
                    s['measurements'][right]['seconds'] for s in samples)
        rows.append(dict(name=name, pd=pd, order_certificate=certificate, oracle=oracle,
                         samples=samples, median_seconds=medians, median_paired_ratios=ratios))
        print(name, {a: round(1000*t, 3) for a, t in medians.items()}, ratios, flush=True)
    args.output.write_text(json.dumps(dict(python=sys.version, platform=platform.platform(),
        archive=args.archive.name, archive_sha256=sha256(args.archive.read_bytes()).hexdigest(),
        member=MEMBER, candidate_sha256=sha256(source).hexdigest(),
        maintained_spin_sha256=sha256((ROOT/'fastunknot/spin_jones.py').read_bytes()).hexdigest(),
        driver_sha256=sha256(Path(__file__).read_bytes()).hexdigest(), seed=26100862,
        rounds=5, excluded_warmups=1, seconds=3, max_states=4096, max_transitions=200000,
        scope='Full Jones on common externally prepared certified order; fresh PD and tensor setup included',
        censoring='Limited times are not completed-query denominators', rows=rows), indent=2)+'\n')


if __name__ == '__main__':
    main()
