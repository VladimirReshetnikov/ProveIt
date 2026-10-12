"""Raw timings: native same-success core kernels and unpruned forest enumeration.

The family is a closed-walk incidence fixture.  Its geometric construction
is in the article; this script does not authenticate it as a normal-cut source.
"""
import argparse
import itertools
import json
from pathlib import Path
import platform
import statistics
import sys
from time import perf_counter_ns


def family_core(h):
    edges, rows = [], []
    for i in range(h):
        v = i + 1
        a, b, c = 3*i, 3*i+1, 3*i+2
        edges.extend(dict(id=e, ends=[0, v]) for e in (a, b, c))
        for walk in ([(0,a),(v,c),(0,b),(v,c)], [(0,b),(v,c)]):
            cycle = []
            for start, edge in walk:
                cycle.extend([dict(dimension=0, handle=start),
                              dict(dimension=1, handle=edge)])
            rows.append(dict(id=len(rows), cycle=cycle))
    return dict(handles0=[dict(id=i) for i in range(h+1)], handles1=edges,
                handles2=rows, handles3=[])


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--fast-dir', type=Path,
                        default=Path('ProveIt/Topology/UnknotRecognition/fast'))
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).with_name('benchmark_deferred.json'))
    parser.add_argument('--native-repeats', type=int, default=9)
    parser.add_argument('--native-passes', type=int, default=25)
    parser.add_argument('--family-max', type=int, default=10)
    args = parser.parse_args()
    root = args.fast_dir.resolve()
    sys.path.insert(0, str(root))
    from fastunknot.core_handlebody import (
        core_handlebody_certificate, _occurrences, column_cancellation_plan)
    from fastunknot.core_handlebody_verify import verify_core_handlebody_certificate
    from fastunknot.core_three_handle_reduction import reduce_core_three_handles
    from fastunknot.normal_parallelity_geometry import _parallelity_geometry
    from fastunknot.normal_surface_geometry import _prepare, _coordinates

    cases = []
    for name in ('corpus.json', 'three_handle_corpus.json'):
        cases.extend(json.loads((root/'marked_parallelity_research'/name).read_text())['cases'])
    common, improved = [], []
    for case in cases:
        p = _prepare(case['triangulation'], lambda:None)
        g = _parallelity_geometry(p, _coordinates(p,case['coordinates'],lambda:None),
                                 lambda:None)
        core = reduce_core_three_handles(g)[0]['core']
        old = core_handlebody_certificate(core, forest_strategy='canonical')
        new = core_handlebody_certificate(core, forest_strategy='deferred')
        if old['status'] == new['status'] == 'COMPLETE':
            common.append((case['id'], core))
        elif old['status'] == 'INCONCLUSIVE' and new['status'] == 'COMPLETE':
            improved.append(case['id'])
    measurements = []
    for repeat in range(args.native_repeats):
        order = ['canonical','deferred'][::1 if repeat%2 == 0 else -1]
        record = dict(repeat=repeat, order=order)
        for strategy in order:
            start = perf_counter_ns()
            for _ in range(args.native_passes):
                for _, core in common:
                    core_handlebody_certificate(core, forest_strategy=strategy)
            record[strategy+'_ns'] = perf_counter_ns() - start
        measurements.append(record)
    totals = {s: statistics.median(r[s+'_ns'] for r in measurements)
              for s in ('canonical','deferred')}
    native = dict(common_success_cases=len(common), extra_success_cases=improved,
                  repeats=args.native_repeats, corpus_passes=args.native_passes,
                  kernel_calls_per_measurement=args.native_passes*len(common),
                  raw_measurements=measurements, median_batch_ns=totals,
                  deferred_over_canonical_ratio=totals['deferred']/totals['canonical'],
                  case_ids=[name for name,_ in common],
                  scope='Source geometry and dual reduction constructed before timer; production core producer only; same-success subset.')
    family = []
    for h in range(1,args.family_max+1):
        core = family_core(h)
        start = perf_counter_ns()
        examined = 0
        for choice in itertools.product(range(3), repeat=h):
            tree = [3*i+c for i,c in enumerate(choice)]
            plan = column_cancellation_plan(_occurrences(core,tree,lambda:None))
            examined += 1
            if not plan['remaining_rows']:
                break
        enumeration_ns = perf_counter_ns() - start
        assert examined == (3**h+1)//2
        assert choice == (1,)*h
        repeats = 101
        start = perf_counter_ns()
        for _ in range(repeats):
            result = core_handlebody_certificate(core,forest_strategy='deferred')
        deferred_ns = (perf_counter_ns()-start)/repeats
        assert result['status'] == 'COMPLETE'
        assert verify_core_handlebody_certificate(core,result['certificate'])
        family.append(dict(h=h, all_forests=3**h, successful_forests=2**h,
                           forests_examined=examined, enumeration_ns=enumeration_ns,
                           deferred_mean_ns=deferred_ns,
                           raw_source_occurrences=6*h, source_incidences=5*h,
                           deferred_stats=result['stats']))
        print('family',h,'examined',examined,'seconds',round(enumeration_ns/1e9,6),flush=True)
    scaling = []
    for h in (16,64,256,1024,4096,16384):
        core = family_core(h)
        raw = []
        for _ in range(5):
            start = perf_counter_ns()
            result = core_handlebody_certificate(core,forest_strategy='deferred')
            raw.append(perf_counter_ns()-start)
        assert result['status'] == 'COMPLETE'
        scaling.append(dict(h=h, raw_ns=raw, median_ns=statistics.median(raw),
                            raw_source_occurrences=6*h,
                            source_incidences=5*h, deferred_stats=result['stats']))
    result = dict(python=sys.version, platform=platform.platform(),
                  native=native, family=family, deferred_scaling=scaling,
                  family_scope='Connected wedge of theta graphs with specified closed walks; no normal-cut source authentication. Enumeration is deliberately unpruned lexicographic enumeration, not a lower bound for all algorithms.')
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print('native', {k:v for k,v in native.items() if k in
                    ('common_success_cases','median_batch_ns','deferred_over_canonical_ratio')})
    print('output',args.output)


if __name__ == '__main__':
    main()
