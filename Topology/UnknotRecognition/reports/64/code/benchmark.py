"""Paired relation-kernel measurements, not knot-recognition timings.

All arms deduplicate exact partitions, index by complementary grade, sort by
cost, and stop each query on its first feasible witness. Source and query
creation is outside the timed region. Report both query-only and end-to-end
(including reduction) costs. An A/A arm and no-compression controls are included.
"""
from collections import defaultdict
from pathlib import Path
import json
import platform
import random
import statistics
import time
from disc_basis import Candidate, reduce_family, grade, star_partition
from reference import partitions, compatible

ROOT = Path(__file__).resolve().parents[1]


def prepare(cs):
    unique = {}
    for c in cs:
        key = (c.control, c.partition)
        if key not in unique or (c.cost, c.id) < (unique[key].cost, unique[key].id):
            unique[key] = c
    tables = defaultdict(list)
    for c in sorted(unique.values(), key=lambda c: (c.cost, c.id)):
        tables[(c.control, grade(c.partition))].append(c)
    return tables


def run_queries(table, queries):
    answers = []
    calls = 0
    for q in queries:
        answer = None
        for c in table.get(('default', len(q)-1-grade(q)), []):
            calls += 1
            if compatible(c.partition, q):
                answer = c.cost
                break
        answers.append(answer)
    return answers, calls


def main():
    rng = random.Random(2026100911)
    specs = []
    for r, count in [(7, 256), (8, 1), (8, 1024), (9, 1024)]:
        ps = list(partitions(r))
        cs = [Candidate(str(i), p, rng.randrange(-10**6, 10**6)) for i, p in enumerate(ps)]
        qs = [rng.choice(ps) for _ in range(count)]
        specs.append((f'full_r{r}_q{count}', r, cs, qs, 'all set partitions; random signed weights and random futures'))
    r = 8
    ps = list(partitions(r))
    ps = [p for p in ps if p[0] == p[1]]
    cs = [Candidate(str(i), p, rng.randrange(-10**6, 10**6)) for i, p in enumerate(ps)]
    qs = [rng.choice(ps) for _ in range(512)]
    specs.append(('common_cycle_r8_q512', r, cs, qs, 'adverse infeasible completions: both sides force labels 0 and 1 together'))
    cs = [Candidate(str(a), star_partition(8, a), a) for a in range(128)]
    qs = [star_partition(8, rng.randrange(128)) for _ in range(256)]
    specs.append(('optimal_star_r8_q256', 8, cs, qs, 'optimal-size family: exterior reduction cannot remove a row'))
    results = []
    for name, r, cs, qs, meaning in specs:
        arms = ['full', 'aa', 'cut', 'exterior']
        samples = []
        expected = run_queries(prepare(cs), qs)[0]
        # One untimed warmup per arm.
        for arm in arms:
            kept = cs if arm in ('full', 'aa') else reduce_family(cs, r, method=arm, certificate=False)[0]
            assert run_queries(prepare(kept), qs)[0] == expected
        for round_no in range(7):
            order = arms[:]
            rng.shuffle(order)
            sample = {'order': order, 'arms': {}}
            for arm in order:
                start = time.perf_counter()
                kept = cs if arm in ('full', 'aa') else reduce_family(cs, r, method=arm, certificate=False)[0]
                table = prepare(kept)
                prepared = time.perf_counter()
                answer, calls = run_queries(table, qs)
                end = time.perf_counter()
                assert answer == expected
                sample['arms'][arm] = {'prepare_seconds': prepared-start,
                                       'query_seconds': end-prepared,
                                       'total_seconds': end-start,
                                       'kept_rows': len(kept), 'graph_tests': calls}
            samples.append(sample)
        summary = {}
        for arm in arms:
            summary[arm] = {key: statistics.median(s['arms'][arm][key] for s in samples)
                            for key in ('prepare_seconds', 'query_seconds', 'total_seconds')}
            summary[arm].update({key: samples[0]['arms'][arm][key] for key in ('kept_rows', 'graph_tests')})
        ratios = {arm: statistics.median(s['arms']['full']['total_seconds']/s['arms'][arm]['total_seconds'] for s in samples)
                  for arm in ('aa', 'cut', 'exterior')}
        result = {'name': name, 'r': r, 'input_rows': len(cs), 'queries': len(qs),
                  'feasible_queries': sum(a is not None for a in expected), 'meaning': meaning,
                  'summary': summary, 'paired_full_over_total': ratios, 'samples': samples}
        results.append(result)
        print(name, 'rows', len(cs), '/', summary['cut']['kept_rows'], '/', summary['exterior']['kept_rows'],
              'full/ext total', round(ratios['exterior'], 3), flush=True)
    output = {'seed': 2026100911, 'python': platform.python_version(), 'platform': platform.platform(),
              'rounds': 7, 'certificate_generation_and_checking_timed': False,
              'native_repository_execution': False, 'fixtures': results}
    (ROOT/'results'/'benchmark.json').write_text(json.dumps(output, indent=2)+'\n')


if __name__ == '__main__':
    main()
