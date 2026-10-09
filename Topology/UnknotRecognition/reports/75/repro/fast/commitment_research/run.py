"""Audit, benchmark, and independently replay the bounded Pachner delivery.

Run from fast/: python -m commitment_research.run audit --output results.json
The standard library and bundled fastunknot code suffice.  Exact geometric
fixtures, measurements, and certificates are retained in the output JSON.
"""
import argparse
from copy import deepcopy
import json
from math import factorial
from pathlib import Path
import platform
import random
import statistics
import time

from fastunknot.pachner_commitments_verify import inspect_pachner_endpoint


def audit():
    from normal_orbit_research.fixtures import layered_torus
    from fastunknot.normal_cocycle import rank_one_cocycle_seed
    from fastunknot.pachner_commitments import search_pachner_endpoints
    from commitment_research.fixtures import independent_bipyramids, endpoint_keys
    cases = []
    for n, u in ((1, 0), (2, 0), (3, 0), (2, 1), (3, 1)):
        raw, _ = layered_torus(n)
        cases.append((f'layered_{n}_up_{u}', raw, rank_one_cocycle_seed(raw)['heights'],
                      dict(max_upward=u)))
    for p in (1, 2):
        f = independent_bipyramids(p)
        cases.append((f'independent_{p}', f['triangulation'], f['heights'], {}))
    f = independent_bipyramids(3)
    for active in ([], f['regions'][0], f['regions'][1], f['regions'][2]):
        cases.append((f'footprint_{active}', f['triangulation'], f['heights'],
                      dict(active_initial_tetrahedra=active)))
    records, replays, mutations = [], 0, 0
    for name, raw, h, options in cases:
        runs, reference = {}, None
        for method in ('naive', 'sleep', 'commitments'):
            answer = search_pachner_endpoints(raw, h, method=method, max_nodes=None,
                                               collect_endpoints=True, **options)
            if answer['status'] != 'COMPLETE_BOUNDED_FAMILY':
                raise AssertionError((name, method, answer['status']))
            keys = endpoint_keys(raw, h, answer['endpoints'])
            if reference is None:
                reference = keys
            elif keys != reference:
                raise AssertionError(('endpoint mismatch', name, method))
            for proof in answer['endpoints']:
                if inspect_pachner_endpoint(raw, h, proof) is None:
                    raise AssertionError(('replay', name, method))
                replays += 1
                bad = deepcopy(proof)
                bad['coordinates'][0][0] += 1
                if inspect_pachner_endpoint(raw, h, bad) is not None:
                    raise AssertionError(('accepted coordinate mutation', name, method))
                mutations += 1
            runs[method] = answer
        records.append(dict(name=name, triangulation=raw, heights=h,
                            options=options, geometric_endpoints=len(reference), runs=runs))
        print(name, {m: a['stats']['nodes'] for m, a in runs.items()}, flush=True)
    path = Path(__file__).with_name('coherent-obstruction-certificate.json')
    old = json.loads(path.read_text())
    raw = old['moves'][-1]['triangulation']
    h = rank_one_cocycle_seed(raw)['heights']
    obstruction = search_pachner_endpoints(raw, h, method='sleep', seek_disc=True)
    if obstruction['status'] != 'DISC_FOUND':
        raise AssertionError('obstruction fixture not resolved')
    summary = inspect_pachner_endpoint(raw, h, obstruction['certificate'])
    if summary is None or not summary['contains_compressing_disk']:
        raise AssertionError('obstruction positive replay')
    replays += 1
    return dict(kind='audit', python=platform.python_version(), cases=records,
                obstruction=dict(triangulation=raw, heights=h, result=obstruction),
                summary=dict(cases=len(records), search_calls=3*len(records)+1,
                             accepted_replays=replays, rejected_mutations=mutations,
                             mismatch_count=0))


def benchmark(repeats):
    from fastunknot.pachner_commitments import search_pachner_endpoints
    from commitment_research.fixtures import independent_bipyramids
    rng = random.Random(202610091337)
    records = []
    for p in range(1, 7):
        f = independent_bipyramids(p)
        raw, h = f['triangulation'], f['heights']
        samples = []
        saved = None
        for round_index in range(-1, repeats):
            order = ['naive', 'sleep']
            rng.shuffle(order)
            timings, measurements = {}, {}
            for method in order:
                start = time.perf_counter_ns()
                answer = search_pachner_endpoints(raw, h, method=method, max_nodes=None,
                                                   collect_endpoints=True)
                elapsed = time.perf_counter_ns()-start
                if answer['status'] != 'COMPLETE_BOUNDED_FAMILY':
                    raise AssertionError('incomplete benchmark')
                timings[method] = elapsed
                measurements[method] = answer['stats']
                if method == 'sleep' and saved is None:
                    saved = answer['endpoints']
            expected = sum(factorial(p)//factorial(p-j) for j in range(p+1))
            if (measurements['naive']['nodes'] != expected
                    or measurements['sleep']['nodes'] != 2**p):
                raise AssertionError(('independent count', p))
            samples.append(dict(round=round_index, warmup=round_index < 0,
                                order=order, nanoseconds=timings, stats=measurements,
                                paired_speedup=timings['naive']/timings['sleep']))
            print('independent', p, 'round', round_index,
                  'ratio', round(timings['naive']/timings['sleep'], 3), flush=True)
        for proof in saved:
            if inspect_pachner_endpoint(raw, h, proof) is None:
                raise AssertionError('saved benchmark proof failed')
        measured = [s for s in samples if not s['warmup']]
        records.append(dict(name=f'independent_{p}', regions=p, tetrahedra=3*p,
                            triangulation=raw, heights=h, construction=f['construction'],
                            samples=samples, certificates=saved,
                            median_naive_ns=statistics.median(
                                s['nanoseconds']['naive'] for s in measured),
                            median_sleep_ns=statistics.median(
                                s['nanoseconds']['sleep'] for s in measured),
                            median_paired_speedup=statistics.median(
                                s['paired_speedup'] for s in measured)))
    return dict(kind='benchmark', python=platform.python_version(),
                repeats=repeats, seed=202610091337, cases=records,
                timing_scope='complete endpoint enumeration, validated transport, and '
                    'certificate copying; fixture construction and external replay excluded',
                caveat='supplied cochain move-family enumeration, not complete knot recognition')


def replay(path):
    data = json.loads(Path(path).read_text())
    checked = 0
    for case in data['cases']:
        if data['kind'] == 'audit':
            proofs = [proof for run in case['runs'].values() for proof in run['endpoints']]
        else:
            proofs = case['certificates']
        for proof in proofs:
            if inspect_pachner_endpoint(case['triangulation'], case['heights'], proof) is None:
                raise AssertionError('saved proof failed')
            checked += 1
    if 'obstruction' in data:
        case = data['obstruction']
        if inspect_pachner_endpoint(case['triangulation'], case['heights'],
                                     case['result']['certificate']) is None:
            raise AssertionError('saved positive proof failed')
        checked += 1
    return dict(kind='independent replay', input=str(path), accepted=checked)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('task', choices=('audit', 'benchmark', 'replay'))
    parser.add_argument('--output', required=True)
    parser.add_argument('--input')
    parser.add_argument('--repeats', type=int, default=3)
    args = parser.parse_args()
    if args.repeats < 1:
        parser.error('--repeats must be positive')
    if args.task == 'replay' and not args.input:
        parser.error('replay requires --input')
    result = audit() if args.task == 'audit' else (
        benchmark(args.repeats) if args.task == 'benchmark' else replay(args.input))
    target = Path(args.output)
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(result, indent=2)+'\n')
    print('saved', target, flush=True)


if __name__ == '__main__':
    main()
