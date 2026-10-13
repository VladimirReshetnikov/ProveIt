"""Paired, source-to-verified-census measurements for deferred forests.

Canonical/deferred timings are compared only on common complete outcomes.
New successes are compared with the explicit Regina whole-cut operation.
These are fixed cut queries, not end-to-end unknot recognition measurements.
"""
import argparse
import hashlib
import json
from pathlib import Path
import platform
import random
import statistics
import sys
from time import perf_counter_ns


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--fast-root', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--rounds', type=int, default=7)
    args = parser.parse_args()
    root = args.fast_root.resolve()
    sys.path.insert(0, str(root))
    import regina
    from fastunknot.normal_cut_handlebodies import normal_cut_handlebodies
    from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies
    from marked_parallelity_research.benchmark_census import explicit
    bank = {}
    for name in ('corpus.json', 'three_handle_corpus.json'):
        bank.update((c['id'], c) for c in json.loads(
            (root/'marked_parallelity_research'/name).read_text())['cases'])
    source_files = ['core_handlebody.py', 'bundle_boundary_kernel.py',
                    'bundle_boundary_kernel_verify.py', 'normal_cut_handlebodies.py']
    pins = {n: hashlib.sha256((root/'fastunknot'/n).read_bytes()).hexdigest()
            for n in source_files}
    common = ['pilot/fibonacci_lst_01/0', 'pilot/fibonacci_lst_03/0',
              'pilot/fibonacci_lst_05/0', 'pilot/fibonacci_lst_07/0',
              'pilot/lst_0_1/0', 'pilot/lst_1_5/0']
    gains = ['pilot/fibonacci_lst_04/0', 'pilot/fibonacci_lst_08/0',
             'pilot/fibonacci_lst_10/0', 'pilot/finite_trefoil/0',
             'interior_loop/empty', 'interior_loop/boundary_link']
    rng = random.Random(2026101201)
    report = dict(python=sys.version, platform=platform.platform(),
                  regina=regina.versionString(), source_sha256=pins,
                  rounds=args.rounds, seed=2026101201, timer='perf_counter_ns',
                  scope='Same authenticated source and fixed normal surface. Native includes production and independent replay; explicit includes source construction, literal cut, and all component recognition. No process startup is timed.',
                  cases=[])

    def native(case, strategy):
        begin = perf_counter_ns()
        value = normal_cut_handlebodies(case['triangulation'], case['coordinates'],
            record_certificate=True, forest_strategy=strategy)
        produced = perf_counter_ns()
        assert value['status'] == 'COMPLETE', (case['id'], strategy, value)
        assert verify_normal_cut_handlebodies(case['triangulation'],
            case['coordinates'], value['certificate'])
        end = perf_counter_ns()
        return value['census']['histogram'], dict(produce_ns=produced-begin,
                                                replay_ns=end-produced,
                                                total_ns=end-begin)

    for name in common + gains:
        case = bank[name]
        group = 'common_success' if name in common else 'new_success'
        other = 'canonical' if group == 'common_success' else 'explicit'
        expected, _ = native(case, 'deferred')
        if other == 'canonical':
            check, _ = native(case, other)
        else:
            old = normal_cut_handlebodies(case['triangulation'],case['coordinates'],
                                         forest_strategy='canonical')
            assert old['status'] == 'INCONCLUSIVE'
            check = explicit(case['triangulation'],case['coordinates'])[0]['histogram']
        assert check == expected
        samples = []
        for _ in range(args.rounds):
            order = ['deferred', other]
            rng.shuffle(order)
            sample = dict(order=order)
            for strategy in order:
                if strategy == 'explicit':
                    value, seconds = explicit(case['triangulation'], case['coordinates'])
                    assert value['histogram'] == expected
                    sample[strategy] = dict(total_ns=seconds*1e9)
                else:
                    value, timing = native(case, strategy)
                    assert value == expected
                    sample[strategy] = timing
            samples.append(sample)
        aa = []
        for _ in range(3):
            _, first = native(case, 'deferred')
            _, second = native(case, 'deferred')
            aa.append(first['total_ns']/second['total_ns'])
        medians = {s: statistics.median(x[s]['total_ns'] for x in samples)
                   for s in ('deferred', other)}
        record = dict(id=name, group=group, histogram=expected, samples=samples,
                      median_total_ns=medians,
                      median_deferred_over_other=statistics.median(
                          s['deferred']['total_ns']/s[other]['total_ns'] for s in samples),
                      deferred_aa_ratios=aa, deferred_aa_median=statistics.median(aa))
        report['cases'].append(record)
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(report,indent=2)+'\n')
        print(json.dumps({k:v for k,v in record.items() if k not in ('samples','deferred_aa_ratios')}),flush=True)
    assert pins == {n: hashlib.sha256((root/'fastunknot'/n).read_bytes()).hexdigest()
                    for n in source_files}
    report['finished'] = True
    args.output.write_text(json.dumps(report,indent=2)+'\n')


if __name__ == '__main__':
    main()
