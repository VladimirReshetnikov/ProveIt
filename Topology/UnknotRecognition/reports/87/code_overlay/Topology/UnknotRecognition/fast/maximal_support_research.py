"""Reproduce maximal-support algebraic and actual-source audits.

Run from fast/: python maximal_support_research.py --output RESULTS.json
The cyclic family is an abstract rational cone, not a claimed realization
as normal matching data. Actual-source audits use the maintained report-57
complete vertex corpus. Timings include exact reconstruction and replay.
Neither timing ratios nor the simplex backends prove polynomial worst-case
running time. The old sufficient reducer has a weaker output contract.
"""

import argparse
from itertools import combinations, product
import json
from math import comb
from pathlib import Path
import platform
import random
from statistics import median
from time import perf_counter

from fastunknot.normal_sector import build_sector_kernel, discover_in_sector
from fastunknot.normal_sector_verify import verify_sector_exhaustion, verify_sector_witness
from fastunknot.sector_matching_support import _combined_closure, matching_support
from fastunknot.sector_maximal_support import (
    certify_nonnegative_kernel_support, certify_maximal_support,
    discover_in_maximal_support_sector,
)
from fastunknot.sector_maximal_support_verify import (
    verify_nonnegative_kernel_support_certificate, verify_maximal_support_certificate,
)
from fastunknot.sector_sparse import PreparedSectorSource


def cyclic_matrix(m, effective):
    return [[int(i == j) for j in range(m)]
            + [int(i == j)-int((i+1) % m == j) for j in range(m)]
            + [0]*(effective-1) for i in range(m)]


def samples(operation, repeats):
    result = None
    elapsed = []
    for _ in range(repeats):
        start = perf_counter()
        result = operation()
        elapsed.append(perf_counter()-start)
    return result, elapsed


def matrix_audit(sizes, repeats):
    records = []
    # Warm optional imports separately. Published per-query timing does not
    # include Python/SciPy import startup; every exact query cost is included.
    certify_nonnegative_kernel_support(cyclic_matrix(3, 1))
    for m in sizes:
        for effective in (1, 3):
            matrix = cyclic_matrix(m, effective)
            closure, old_times = samples(lambda: _combined_closure(matrix, lambda: None), repeats)
            result, new_times = samples(lambda: certify_nonnegative_kernel_support(matrix), repeats)
            assert closure == (set(), [])
            assert result['status'] == 'COMPLETE'
            assert result['retained_indices'] == list(range(m, 2*m+effective-1))
            assert result['stats']['effective_dimension'] == effective
            proof = result['certificate']
            replay, replay_times = samples(
                lambda: verify_nonnegative_kernel_support_certificate(matrix, proof), repeats)
            assert replay
            raw_dimension = m+effective-1
            records.append(dict(m=m, coordinates=2*m+effective-1,
                raw_dimension=raw_dimension, effective_dimension=effective,
                pair_closure_forced=0, exact_forced=m,
                raw_coordinate_arrangement_bases=str(comb(2*m+effective-1, raw_dimension-1)),
                effective_distinct_Q_hyperplanes=effective, exact_Q_rays=effective,
                pair_closure_seconds=old_times, certifier_seconds=new_times,
                replay_seconds=replay_times, stats=result['stats'], certificate=proof))
    return records


def source_supports(record):
    count = len(record['triangulation']['tetrahedra'])
    supports = {()}
    for field in ('standard_vertices', 'quad_vertices'):
        supports.update(tuple((t, q) for t, row in enumerate(s['coordinates'])
                              for q in range(3) if row[4+q]) for s in record[field])
    if count <= 3:
        supports.update(tuple((t, q) for t, q in enumerate(types) if q >= 0)
                        for types in product((-1, 0, 1, 2), repeat=count))
    else:
        for size in (1, 2):
            for indices in combinations(range(count), size):
                supports.update(tuple(zip(indices, types))
                                for types in product(range(3), repeat=size))
        rng = random.Random('sector-envelope-v1:'+record['id'])
        supports.update(tuple((t, rng.randrange(3)) for t in range(count)) for _ in range(64))
    return sorted(supports)


def source_audit(bank):
    records = []
    for record in bank['records']:
        raw = record['triangulation']
        source = PreparedSectorSource(raw)
        for support in source_supports(record):
            kernel = source.build(support)
            if len(kernel.basis) <= 3:
                continue
            started = perf_counter()
            incumbent_keep, _ = matching_support(kernel, lambda: None)
            old_seconds = perf_counter()-started
            started = perf_counter()
            result = certify_maximal_support(raw, support, source=source)
            elapsed = perf_counter()-started
            assert result['status'] == 'COMPLETE', (record['id'], support, result)
            assert verify_maximal_support_certificate(raw, support, result['certificate'])
            admitted = [s['coordinates'] for s in record['standard_vertices']
                        if all(not row[4+q] or (t, q) in support
                               for t, row in enumerate(s['coordinates']) for q in range(3))]
            expected = [j for j, (t, q) in enumerate(support)
                        if any(rows[t][4+q] for rows in admitted)]
            assert expected == result['retained_indices'], (record['id'], support, expected, result)
            assert set(expected) <= set(incumbent_keep)
            records.append(dict(source=record['id'], support=support,
                raw_dimension=len(kernel.basis), effective_dimension=result['stats']['effective_dimension'],
                exact_retained=expected, incumbent_retained=incumbent_keep,
                extra_forced_by_complete_LP=sorted(set(incumbent_keep)-set(expected)),
                certificate_seconds=elapsed, incumbent_reducer_seconds=old_seconds,
                solver=result['stats']['solver']))
    return records


def discovery_timings(bank, repeats):
    by_id = {record['id']: record for record in bank['records']}
    cases = [
        ('cap_3_5_2', [(0, 0), (1, 1), (2, 2), (3, 0), (4, 1)]),
        ('cap_3_5_3', [(0, 0), (1, 1), (2, 2), (3, 0), (4, 2), (5, 2)]),
        ('cap_1_2_3', [(t, 0) for t in range(4)]),
        ('fibonacci_lst_09', [(t, (0, 2, 1)[t % 3]) for t in range(9)]),
        ('fibonacci_lst_09', [(t, 2) for t in range(9)]),
    ]
    records = []
    for source_id, support in cases:
        raw = by_id[source_id]['triangulation']
        # One warm-up in each arm, then alternating complete calls. These
        # include source preparation, solver/reconstruction/replay, geometry
        # and any disk observers reached by the configured standard query.
        discover_in_sector(raw, support, phase='standard')
        discover_in_maximal_support_sector(raw, support)
        times = [[], []]
        answers = [None, None]
        operations = [lambda: discover_in_sector(raw, support, phase='standard'),
                      lambda: discover_in_maximal_support_sector(raw, support)]
        for repetition in range(repeats):
            for arm in ((0, 1) if repetition % 2 == 0 else (1, 0)):
                started = perf_counter(); answers[arm] = operations[arm]()
                times[arm].append(perf_counter()-started)
        assert answers[0]['status'] == answers[1]['status']
        for answer in answers:
            verifier = verify_sector_witness if answer['status'] == 'DISC_FOUND' else verify_sector_exhaustion
            assert verifier(raw, answer['certificate'])
        records.append(dict(source=source_id, support=support, status=answers[1]['status'],
            incumbent_seconds=times[0], maximal_support_seconds=times[1],
            median_ratio_new_over_old=median(times[1])/median(times[0]),
            incumbent_stats=answers[0]['stats'], maximal_support_stats=answers[1]['stats'],
            maximal_support_certificate=answers[1]['maximal_support_certificate']))
    return records


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--sizes', default='3,8,16,32,64')
    parser.add_argument('--repeats', type=int, default=3)
    parser.add_argument('--bank', type=Path,
                        default=Path(__file__).resolve().parents[1]/'reports/57/results/discovery_corpus.json')
    args = parser.parse_args()
    if args.repeats < 1:
        parser.error('repeats must be positive')
    sizes = [int(x) for x in args.sizes.split(',')]
    if any(x < 3 for x in sizes):
        parser.error('cyclic obstruction requires m >= 3')
    bank = json.loads(args.bank.read_text())
    result = dict(schema='maximal-support-research-v1', python=platform.python_version(),
                  platform=platform.platform(), repeats=args.repeats,
                  abstract_scope='rational matching cones; no asserted triangulation realization',
                  source_scope='supplied finite triangulations; no diagram-wide QP claim',
                  timing_scope='warm imports; exact producer and independent replay included',
                  polynomial_solver_guarantee=False)
    result['abstract'] = matrix_audit(sizes, args.repeats)
    result['sources'] = source_audit(bank)
    result['discovery'] = discovery_timings(bank, args.repeats)
    result['source_summary'] = dict(
        audited=len(result['sources']),
        reduced=sum(r['raw_dimension'] > r['effective_dimension'] for r in result['sources']),
        stronger_than_pair_closure=sum(bool(r['extra_forced_by_complete_LP']) for r in result['sources']),
        raw_dimensions=sorted({r['raw_dimension'] for r in result['sources']}),
        effective_dimensions=sorted({r['effective_dimension'] for r in result['sources']}))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result['source_summary']))
    print(json.dumps([dict(source=r['source'], ratio=r['median_ratio_new_over_old'])
                      for r in result['discovery']]))


if __name__ == '__main__':
    main()
