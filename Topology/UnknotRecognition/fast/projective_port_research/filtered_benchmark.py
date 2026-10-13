"""Complete accepted-extreme searches, with equivalent geometric answers."""
from hashlib import sha256
import json
import platform
import random
import statistics
import sys
import time

from .common import source_hashes
from .filtered_native import cases, workload, encode, save


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
    rng = random.Random(17220261012)
    selected = {'two_tet_0','two_tet_7','two_tet_15','capped_2_1','capped_4_1'}
    report = dict(passed=False, source_sha256=source_hashes(), python=sys.version,
        platform=platform.platform(), records=[],
        scope='complete accepted-positive-extreme search on each anchor face; includes source validation, source/kernel compilation, full preparation, all queries and recovery, geometric inspection with a per-arm per-source witness cache, independent certificate replay and JSON; excludes fixture construction; supplied triangulations only')
    for case in cases():
        if case['id'] not in selected:
            continue
        warm = {arm:measure(case,arm) for arm in ('native','filtered')}
        assert warm['native']['answers'] == warm['filtered']['answers']
        samples = []
        for _ in range(7):
            order = ['native','filtered']
            rng.shuffle(order)
            result = {}
            for arm in order:
                result[arm] = measure(case,arm)
                assert result[arm]['output_sha256'] == warm[arm]['output_sha256']
            samples.append(dict(order=order, arms=result))
        aa = []
        for _ in range(3):
            a,b = measure(case,'filtered'),measure(case,'filtered')
            assert a['output_sha256']==b['output_sha256']==warm['filtered']['output_sha256']
            aa.append(dict(a_ms=a['ms'],b_ms=b['ms']))
        medians = {arm:statistics.median(s['arms'][arm]['ms'] for s in samples) for arm in warm}
        ratio = statistics.median(s['arms']['filtered']['ms']/s['arms']['native']['ms'] for s in samples)
        record = dict(id=case['id'], warmup=warm, samples=samples, duplicate_samples=aa,
            median_ms=medians, paired_filtered_over_native=ratio,
            duplicate_median_ratio=statistics.median(x['a_ms']/x['b_ms'] for x in aa))
        report['records'].append(record)
        save(sys.argv[1],report)
        print(case['id'], medians, ratio, flush=True)
    report['passed'] = True
    save(sys.argv[1],report)


if __name__ == '__main__':
    main()
