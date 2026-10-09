"""Paired, source-pinned LP-screening audit with explicit resource limits.

Run from fast/: python -m lp_cache_research.audit --output lp_cache_research/results.json
No integration default or source fixture is modified.  The synthetic family
is labeled algebraic; every genuine certificate is independently verified.
"""

import argparse
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import platform
from statistics import median
import time

from fastunknot.integer_codec import json_safe
from fastunknot.normal_propagation import search_positive_euler as baseline
from fastunknot.normal_propagation_cached import search_positive_euler as screened
from fastunknot.normal_propagation_verify import verify_normal_propagation_certificate
from lp_cache_research.synthetic_family import run as synthetic_run
from normal_orbit_research.fixtures import layered_torus, export_triangulation


ROOT = Path(__file__).resolve().parents[1]


def digest(value):
    return sha256(json.dumps(json_safe(value), sort_keys=True,
                             separators=(',', ':')).encode()).hexdigest()


def source_pins():
    names = ('fastunknot/normal_propagation.py', 'fastunknot/normal_propagation_cached.py',
             'fastunknot/exact_lp.py', 'fastunknot/normal_propagation_verify.py',
             'lp_cache_research/synthetic_family.py', 'lp_cache_research/triangulations.json')
    return {name: sha256((ROOT/name).read_bytes()).hexdigest() for name in names}


def case_inputs(figure_pivots):
    inputs = []
    for t in (1, 2, 4, 6, 8):
        raw, _ = layered_torus(t)
        inputs.append(dict(name=f'layered_{t}', kind='genuine_triangulation',
                           triangulation=raw, options=dict(max_pivots=None)))
    fixtures = json.loads((ROOT/'lp_cache_research/triangulations.json').read_text())
    for name in ('branching_torus', 'finite_trefoil'):
        inputs.append(dict(name=name, kind='genuine_triangulation',
                           triangulation=fixtures[name]['triangulation'],
                           options=dict(max_pivots=None)))
    for name in ('frozen_figure-eight', 'frozen_figure-eight-relabeled'):
        inputs.append(dict(name=name, kind='genuine_triangulation',
                           triangulation=fixtures[name]['triangulation'],
                           options=dict(max_pivots=figure_pivots)))
    if importlib.util.find_spec('regina'):
        import regina
        tri = regina.Example3.figureEight()
        ideal_sig = tri.isoSig()
        tri.idealToFinite()
        tri.simplify()
        raw = export_triangulation(tri)
        inputs.append(dict(name='native_figure_eight_regenerated', kind='genuine_triangulation',
                           triangulation=raw, options=dict(max_pivots=figure_pivots),
                           provenance=dict(regina_version=regina.versionString(),
                                           recipe='Example3.figureEight; idealToFinite; simplify',
                                           ideal_iso_sig=ideal_sig, iso_sig=tri.isoSig(),
                                           valid=tri.isValid(), orientable=tri.isOrientable(),
                                           ideal=tri.isIdeal(), vertices=tri.countVertices(),
                                           boundary_components=tri.countBoundaryComponents(),
                                           is_solid_torus=tri.isSolidTorus(),
                                           matches_saved_native=raw == fixtures['figure_eight_native']['triangulation'])))
    for size in (1, 2, 4, 6, 8):
        inputs.append(dict(name=f'algebraic_{size}', kind='algebraic_cone', size=size))
    return inputs


def measure(case, cached, timeout):
    start = time.perf_counter()

    def check():
        if time.perf_counter()-start > timeout:
            raise TimeoutError('per-run wall-time allowance exhausted')

    try:
        if case['kind'] == 'algebraic_cone':
            answer = synthetic_run(case['size'], cached=cached, check=check)
        else:
            answer = (screened if cached else baseline)(case['triangulation'],
                                                        check=check, **case['options'])
        search_seconds = time.perf_counter()-start
        proof = answer.get('certificate')
        verified = None
        verify_seconds = None
        if proof is not None and case['kind'] == 'genuine_triangulation':
            verify_start = time.perf_counter()
            verified = verify_normal_propagation_certificate(case['triangulation'], proof)
            verify_seconds = time.perf_counter()-verify_start
            if not verified:
                raise AssertionError('an independently checked genuine certificate was rejected')
        result = dict(status=answer['status'], search_seconds=search_seconds,
                      verify_seconds=verify_seconds, verified=verified,
                      stats=answer['stats'], limits=answer['limits'],
                      reason=answer.get('reason'),
                      certificate_sha256=None if proof is None else digest(proof))
        return result, proof
    except TimeoutError as error:
        return dict(status='WALL_TIMEOUT', search_seconds=time.perf_counter()-start,
                    reason=str(error), verified=None, stats=None,
                    certificate_sha256=None), None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--rounds', type=int, default=3)
    parser.add_argument('--timeout', type=float, default=40)
    parser.add_argument('--figure-pivots', type=int, default=600)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--case', action='append', help='optional exact case-name filter')
    args = parser.parse_args()
    if args.rounds < 1 or args.timeout <= 0 or args.figure_pivots < 0:
        parser.error('rounds/time must be positive, and the pivot allowance nonnegative')
    pins = source_pins()
    cases = case_inputs(args.figure_pivots)
    if args.case:
        cases = [case for case in cases if case['name'] in args.case]
    report = dict(schema='normal-propagation-witness-screening-audit-v1',
                  python=platform.python_version(), platform=platform.platform(),
                  source_sha256=pins, rounds=args.rounds, wall_seconds_per_run=args.timeout,
                  figure_eight_pivots_per_run=args.figure_pivots, cases=[])
    started = time.perf_counter()
    for case in cases:
        record = dict(case, input_sha256=digest(case.get('triangulation',
                                                       {'algebraic_family': case.get('size')})),
                      samples=[])
        for trial in range(args.rounds):
            samples, proofs = {}, {}
            for label in (('baseline', 'screened') if trial % 2 == 0 else ('screened', 'baseline')):
                measurement, proof = measure(case, label == 'screened', args.timeout)
                samples[label], proofs[label] = measurement, proof
            baseline_sample, screened_sample = samples['baseline'], samples['screened']
            complete = all(samples[label]['status'] in ('POSITIVE_EULER', 'NO_POSITIVE_EULER')
                           for label in ('baseline', 'screened'))
            if complete:
                if proofs['baseline'] != proofs['screened']:
                    raise AssertionError('completed certificates differ')
                record.setdefault('certificate', proofs['screened'])
            if baseline_sample['stats'] is not None and screened_sample['stats'] is not None:
                # Count differences are only directly comparable along an
                # identical logical trace, not after unequal budget exhaustion.
                common_trace = all(baseline_sample['stats'][key] == screened_sample['stats'][key]
                                   for key in ('nodes', 'propagations', 'branches', 'anchors_started',
                                               'anchors_completed'))
            else:
                common_trace = False
            samples['complete_certificates_equal'] = True if complete else None
            samples['common_trace_counts'] = common_trace
            record['samples'].append(samples)
            print(case['name'], trial+1, baseline_sample['status'], screened_sample['status'],
                  round(baseline_sample['search_seconds'], 6),
                  round(screened_sample['search_seconds'], 6), flush=True)
            report['elapsed_seconds'] = time.perf_counter()-started
            # Preserve completed cases and current partial measurements.
            args.output.write_text(json.dumps(json_safe(dict(report, cases=report['cases']+[record])),
                                              indent=2)+'\n')
        record['median_search_seconds'] = {
            label: median(sample[label]['search_seconds'] for sample in record['samples'])
            for label in ('baseline', 'screened')}
        if all(sample['common_trace_counts'] for sample in record['samples']):
            medians = record['median_search_seconds']
            record['median_speedup'] = medians['baseline']/medians['screened']
        report['cases'].append(record)
    report['elapsed_seconds'] = time.perf_counter()-started
    if source_pins() != pins:
        raise AssertionError('sources changed during the paired audit')
    args.output.write_text(json.dumps(json_safe(report), indent=2)+'\n')
    print('saved', args.output, round(report['elapsed_seconds'], 3), flush=True)


if __name__ == '__main__':
    main()
