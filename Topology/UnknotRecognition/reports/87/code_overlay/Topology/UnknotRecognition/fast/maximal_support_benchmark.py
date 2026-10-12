"""Isolated paired complete-query timings with an identical-code control.

Run only while other research workers are idle. Each case has fresh-source,
shared-prepared-source, and identical-incumbent control arms. A fixed seed
shuffles arm order within each paired repetition. Solver imports are warm.
Independent exhaustion replay after the trials is outside their timed region;
all verification performed by the actual queried APIs remains inside it.
"""

import argparse
from importlib.metadata import version
import json
from pathlib import Path
import platform
import random
from statistics import median
from time import perf_counter

from fastunknot.normal_sector import _discover_in_kernel, discover_in_sector
from fastunknot.normal_sector_verify import verify_sector_exhaustion, verify_sector_witness
from fastunknot.sector_maximal_support import discover_in_maximal_support_sector
from fastunknot.sector_sparse import PreparedSectorSource


def cases(bank, fixture):
    by_id = {record['id']: record for record in bank['records']}
    simple = [
        ('cap_3_5_2', [(0, 0), (1, 1), (2, 2), (3, 0), (4, 1)]),
        ('cap_3_5_3', [(0, 0), (1, 1), (2, 2), (3, 0), (4, 2), (5, 2)]),
        ('cap_1_2_3', [(t, 0) for t in range(4)]),
        ('fibonacci_lst_09', [(t, (0, 2, 1)[t % 3]) for t in range(9)]),
        ('fibonacci_lst_09_meridian', [(t, 2) for t in range(9)]),
    ]
    for name, support in simple:
        key = 'fibonacci_lst_09' if name.endswith('_meridian') else name
        yield name, by_id[key]['triangulation'], support
    yield 'pachner_36_fixed_row_miss', fixture['specification']['triangulation'], fixture['allowed_types']


def run_case(name, raw, support, repeats, seed):
    source = PreparedSectorSource(raw)
    old_shared = lambda: _discover_in_kernel(source.build(support), phase='standard')
    new_shared = lambda: discover_in_maximal_support_sector(raw, support, source=source)
    modes = [
        ('fresh-source', lambda: discover_in_sector(raw, support, phase='standard'),
                         lambda: discover_in_maximal_support_sector(raw, support)),
        ('prepared-source', old_shared, new_shared),
        ('identical-incumbent-control', old_shared, old_shared),
    ]
    records = []
    for mode, left, right in modes:
        left(); right()
        rng = random.Random(seed+':'+name+':'+mode)
        operations = [left, right]
        times = [[], []]
        answers = [None, None]
        orders = []
        for repetition in range(repeats):
            order = [0, 1]
            rng.shuffle(order)
            orders.append(order)
            for arm in order:
                started = perf_counter()
                answers[arm] = operations[arm]()
                times[arm].append(perf_counter()-started)
        assert answers[0]['status'] == answers[1]['status']
        for answer in answers:
            verifier = verify_sector_witness if answer['status'] == 'DISC_FOUND' else verify_sector_exhaustion
            assert verifier(raw, answer['certificate'])
        if mode == 'identical-incumbent-control':
            assert answers[0]['certificate'] == answers[1]['certificate']
        paired = [b/a for a, b in zip(*times)]
        records.append(dict(mode=mode, order=orders, left_seconds=times[0], right_seconds=times[1],
            paired_ratios=paired, median_paired_ratio=median(paired),
            ratio_of_medians=median(times[1])/median(times[0]),
            left_median_seconds=median(times[0]), right_median_seconds=median(times[1]),
            status=answers[1]['status'], left_stats=answers[0]['stats'], right_stats=answers[1]['stats']))
        print(json.dumps(dict(case=name, mode=mode, ratio=records[-1]['median_paired_ratio'])), flush=True)
    return dict(name=name, support=support, tetrahedra=len(raw['tetrahedra']),
                source_sha256=source.source_sha256, measurements=records)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--repeats', type=int, default=9)
    parser.add_argument('--seed', default='maximal-support-final-20261012')
    parser.add_argument('--bank', type=Path,
                        default=Path(__file__).resolve().parents[1]/'reports/57/results/discovery_corpus.json')
    parser.add_argument('--fixture', type=Path,
                        default=Path(__file__).resolve().parent/'tests/fixtures/maximal_support_pachner_36.json')
    args = parser.parse_args()
    if args.repeats < 7:
        parser.error('final benchmark requires at least seven paired repetitions')
    bank = json.loads(args.bank.read_text())
    fixture = json.loads(args.fixture.read_text())
    result = dict(schema='maximal-support-paired-benchmark-v1', repeats=args.repeats,
        seed=args.seed, python=platform.python_version(), platform=platform.platform(),
        dependencies={name: version(name) for name in ('scipy', 'sympy')},
        timing_scope='warm imports; complete calls; external final exhaustion replay excluded',
        source_scope='supplied sectors, not full knot-diagram recognition',
        cases=[])
    for name, raw, support in cases(bank, fixture):
        result['cases'].append(run_case(name, raw, support, args.repeats, args.seed))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')


if __name__ == '__main__':
    main()
