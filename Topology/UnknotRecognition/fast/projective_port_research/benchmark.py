"""Paired Euler-query batches; chosen witnesses need not be essential discs."""
from hashlib import sha256
import json
import platform
import random
import statistics
import sys
import time

from .common import encode, save, source_hashes
from .native import cases, workload


def measured(case, arm):
    start = time.perf_counter_ns()
    result = workload(case['triangulation'], case['support'], arm)
    wire = json.dumps(result, default=encode, sort_keys=True).encode()
    elapsed = (time.perf_counter_ns()-start)/1e6
    answers = [(a['positive'], None if a['certificate'] is None else
                a['certificate']['contains_compressing_disk']) for a in result['answers']]
    return dict(ms=elapsed, answers=answers, stats=result['stats'], bytes=len(wire),
                output_sha256=sha256(wire).hexdigest())


def main():
    rng = random.Random(11320261012)
    selected = {'two_tet_0', 'two_tet_7', 'two_tet_15', 'capped_2_1', 'capped_4_1'}
    report = dict(passed=False, source_sha256=source_hashes(), python=sys.version,
        platform=platform.platform(), trials=7, duplicate_trials=3,
        scope='full supplied-sector Euler batches: source validation, compilation/kernel, all preparation, seven/eleven/nineteen anchored queries, positive source recovery, independent native disc replay, JSON; excludes fixture construction; compares Euler positivity only: chosen witnesses can have different disc properties; no complete disc search or knot recognition',
        records=[])
    for case in cases():
        if case['id'] not in selected:
            continue
        warm = {a:measured(case, a) for a in ('native', 'delivered', 'intrinsic')}
        expected = [a[0] for a in warm['native']['answers']]
        assert all([a[0] for a in r['answers']]==expected for r in warm.values())
        samples = []
        for trial in range(7):
            order = ['native', 'delivered', 'intrinsic']
            rng.shuffle(order)
            sample = dict(order=order, arms={})
            for arm in order:
                result = measured(case, arm)
                assert [a[0] for a in result['answers']] == expected
                assert result['answers'] == warm[arm]['answers']
                assert result['output_sha256'] == warm[arm]['output_sha256']
                sample['arms'][arm] = result
            samples.append(sample)
        aa = []
        for _ in range(3):
            a, b = measured(case, 'intrinsic'), measured(case, 'intrinsic')
            assert a['output_sha256']==b['output_sha256']==warm['intrinsic']['output_sha256']
            aa.append(dict(a_ms=a['ms'], b_ms=b['ms']))
        medians = {arm:statistics.median(s['arms'][arm]['ms'] for s in samples) for arm in warm}
        ratios = {arm:statistics.median(s['arms'][arm]['ms']/s['arms']['intrinsic']['ms'] for s in samples)
                  for arm in ('native', 'delivered')}
        record = dict(id=case['id'], samples=samples, duplicate_samples=aa, warmup=warm,
                      median_ms=medians, paired_median_ratios=ratios,
                      duplicate_median_ratio=statistics.median(s['a_ms']/s['b_ms'] for s in aa))
        report['records'].append(record)
        save(sys.argv[1], report)
        print(case['id'], medians, ratios, flush=True)
    report['passed'] = True
    save(sys.argv[1], report)


if __name__ == '__main__':
    main()
