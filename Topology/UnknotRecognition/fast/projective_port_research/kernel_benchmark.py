"""Seeded three-arm full-workload timings; preserves historical filtered source."""
from hashlib import sha256
import json
import platform
import random
import statistics
import sys
import time

from .kernel_native import cases, workload, encode, save, hashes


def measure(case, arm):
    start = time.perf_counter_ns()
    result = workload(case, arm)
    wire = json.dumps(result, default=encode, sort_keys=True).encode()
    ms = (time.perf_counter_ns()-start)/1e6
    return dict(ms=ms, output_sha256=sha256(wire).hexdigest(), bytes=len(wire),
        answers=[a['result']['status'] for a in result['answers']],
        inspections=result['unique_inspections'],
        queries=sum(a['result'].get('queries', 0) for a in result['answers']))


def main():
    rng = random.Random(17320261012)
    selected = {'two_tet_0','two_tet_7','two_tet_15','capped_2_1','capped_4_1'}
    arms = ('native', 'filtered', 'kernel')
    report = dict(passed=False, source_sha256=hashes(), python=sys.version,
        platform=platform.platform(), records=[],
        scope='all preparation, independent source-kernel construction, anchor queries, source recovery and checking, native geometry and its independent replay, JSON; per-arm per-source empty witness cache; fixture construction excluded; equivalent complete geometric status, trajectories may differ')
    for case in cases():
        if case['id'] not in selected:
            continue
        warm = {a:measure(case,a) for a in arms}
        if any(warm[a]['answers'] != warm['native']['answers'] for a in arms):
            raise ArithmeticError('warmup answers differ')
        samples = []
        for _ in range(7):
            order = list(arms)
            rng.shuffle(order)
            result = {a:measure(case,a) for a in order}
            for a in arms:
                if result[a]['output_sha256'] != warm[a]['output_sha256']:
                    raise ArithmeticError('nondeterministic output')
            samples.append(dict(order=order, arms=result))
        aa = []
        for _ in range(3):
            a,b = measure(case,'kernel'),measure(case,'kernel')
            if a['output_sha256'] != b['output_sha256'] or a['output_sha256'] != warm['kernel']['output_sha256']:
                raise ArithmeticError('duplicate output differs')
            aa.append(dict(a_ms=a['ms'],b_ms=b['ms']))
        medians = {a:statistics.median(s['arms'][a]['ms'] for s in samples) for a in arms}
        record = dict(id=case['id'], warmup=warm, samples=samples, duplicate_samples=aa,
            median_ms=medians,
            paired_kernel_over_filtered=statistics.median(s['arms']['kernel']['ms']/s['arms']['filtered']['ms'] for s in samples),
            paired_kernel_over_native=statistics.median(s['arms']['kernel']['ms']/s['arms']['native']['ms'] for s in samples),
            duplicate_median_ratio=statistics.median(x['a_ms']/x['b_ms'] for x in aa))
        report['records'].append(record)
        save(sys.argv[1],report)
        print(case['id'], medians, record['paired_kernel_over_filtered'], flush=True)
    report['passed'] = True
    save(sys.argv[1],report)


if __name__ == '__main__':
    main()
