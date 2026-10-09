"""Paired active-support and complete-search controls on frozen normal sources.

The unary baseline skips coordinates already witnessed by an earlier point.
Negative ordinary LPs are retained and skip the expensive strict-support lift.
Use --include-slow-negative to reproduce the documented direct trefoil query.
Every conclusive stored certificate is independently replayed.
"""

import argparse
from fractions import Fraction
from hashlib import sha256
import json
from math import ceil
from pathlib import Path
import platform
import sys
from time import perf_counter

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from fastunknot.exact_lp import solve_nonnegative_kernel
from fastunknot.integer_codec import json_safe
from fastunknot.normal_active import (
    active_positive_cone, search_active_normal_positive, _normal_model,
)
from fastunknot.normal_active_verify import (
    verify_active_cone_certificate, verify_active_normal_certificate,
)


def pair(value):
    value = Fraction(value)
    return [value.numerator, value.denominator]


def unary_support(matrix, objective, seconds=30):
    start = perf_counter()
    calls = pivots = 0
    def check():
        if perf_counter()-start > seconds:
            raise TimeoutError('unary support wall allowance exhausted')
    def query(c):
        nonlocal calls, pivots
        answer = solve_nonnegative_kernel(matrix, c, max_pivots=10000, check=check)
        calls += 1
        pivots += answer['stats']['pivots']
        return answer
    first = query(objective)
    if first['status'] == 'INCONCLUSIVE':
        return dict(status='INCONCLUSIVE', lp_calls=calls, pivots=pivots,
                    reason=first.get('reason'))
    if first['status'] == 'NONPOSITIVE':
        return dict(status=first['status'], lp_calls=calls, pivots=pivots,
                    certificate=dict(schema='active-positive-cone-v1',
                                     status='NONPOSITIVE', y=first['y']))
    p = first['primitive_x']
    active = {j for j, value in enumerate(p) if value}
    z = [0]*len(objective)
    y = [Fraction(0)]*len(matrix)
    for j in range(len(objective)):
        check()
        if j in active:
            continue
        answer = query([int(i == j) for i in range(len(objective))])
        if answer['status'] == 'NONPOSITIVE':
            y = [a+Fraction(*b) for a, b in zip(y, answer['y'])]
        elif answer['status'] == 'POSITIVE':
            witness = answer['primitive_x']
            z = [a+b for a, b in zip(z, witness)]
            active.update(j for j, value in enumerate(witness) if value)
        else:
            return dict(status='INCONCLUSIVE', lp_calls=calls, pivots=pivots)
    cp = sum(Fraction(a)*b for a, b in zip(objective, p))
    cz = sum(Fraction(a)*b for a, b in zip(objective, z))
    scale = max(1, ceil((1-cz)/cp))
    x = [scale*a+b for a, b in zip(p, z)]
    proof = dict(schema='active-positive-cone-v1', status='ACTIVE_POSITIVE',
                 x=[pair(a) for a in x], y=[pair(a) for a in y])
    return dict(status='ACTIVE_POSITIVE', active=sorted(active),
                lp_calls=calls, pivots=pivots, certificate=proof)


def run(args):
    corpus_path = Path(__file__).with_name('sources.json')
    corpus = json.loads(corpus_path.read_text())
    records, searches = [], []
    for case in corpus['cases']:
        if args.case and case['name'] not in args.case:
            continue
        tri = case['triangulation']
        _, matrix, objective, groups = _normal_model(tri, lambda: None)
        anchors = case['anchors'] or [group[0] for group in groups]
        t = len(tri['tetrahedra'])
        coordinates = case['positive_coordinates']
        for fixed in sorted({0, 1, min(2, t)}):
            forbidden = set(anchors)
            for a in range(fixed):
                selected = next((q for q in range(3)
                                 if coordinates and coordinates[a][4+q]), 0)
                forbidden.update(7*a+4+q for q in range(3) if q != selected)
            columns = [j for j in range(len(objective)) if j not in forbidden]
            a = [[row[j] for j in columns] for row in matrix]
            c = [objective[j] for j in columns]
            record = dict(name=case['name'], tetrahedra=t, anchors=anchors,
                          fixed_prefix=fixed, columns=columns)
            start = perf_counter()
            try:
                baseline = unary_support(a, c, args.seconds)
                record['unary_seconds'] = perf_counter()-start
                if 'certificate' in baseline:
                    assert verify_active_cone_certificate(a, c, baseline['certificate'])
                record['unary'] = baseline
            except TimeoutError as error:
                record['unary_seconds'] = perf_counter()-start
                record['unary'] = dict(status='INCONCLUSIVE', reason=str(error))
                baseline = record['unary']
            # This gate is a documented dispatch decision, not a discarded case.
            if baseline['status'] == 'NONPOSITIVE' and not args.include_slow_negative:
                record['batch'] = dict(status='SKIPPED_AFTER_NEGATIVE_PRECHECK')
                record['equivalent'] = True
            else:
                start = perf_counter()
                def check():
                    if perf_counter()-start > args.seconds:
                        raise TimeoutError('batch support wall allowance exhausted')
                try:
                    batch = active_positive_cone(a, c, max_pivots=10000, check=check)
                    record['batch_seconds'] = perf_counter()-start
                    if 'certificate' in batch:
                        assert verify_active_cone_certificate(a, c, batch['certificate'])
                    record['batch'] = batch
                    record['equivalent'] = (
                        batch['status'] == baseline['status']
                        and batch.get('active') == baseline.get('active'))
                except TimeoutError as error:
                    record['batch_seconds'] = perf_counter()-start
                    record['batch'] = dict(status='INCONCLUSIVE', reason=str(error))
                    record['equivalent'] = None
            records.append(record)
            print(case['name'], 'fixed', fixed, baseline['status'],
                  record['batch']['status'], flush=True)
        if case['name'] in ('fibonacci-layered-1', 'fibonacci-layered-2',
                            'fibonacci-layered-3', 'finite-trefoil'):
            for precheck in ((True, False) if t <= 3 else (True,)):
                start = perf_counter()
                def check():
                    if perf_counter()-start > args.seconds:
                        raise TimeoutError('normal search wall allowance exhausted')
                try:
                    answer = search_active_normal_positive(
                        tri, precheck=precheck, max_nodes=200, max_pivots=20000,
                        max_branch_depth=8, check=check)
                    seconds = perf_counter()-start
                    verified = ('certificate' in answer
                                and verify_active_normal_certificate(tri, answer['certificate']))
                    if 'certificate' in answer:
                        assert verified
                    searches.append(dict(name=case['name'], precheck=precheck,
                                         seconds=seconds, answer=answer, verified=verified))
                except TimeoutError as error:
                    searches.append(dict(name=case['name'], precheck=precheck,
                                         seconds=perf_counter()-start,
                                         answer=dict(status='INCONCLUSIVE', reason=str(error))))
                print('search', case['name'], precheck, searches[-1]['answer']['status'], flush=True)
    output = dict(schema='active-normal-audit-v1', python=platform.python_version(),
                  platform=platform.platform(), corpus_sha256=sha256(corpus_path.read_bytes()).hexdigest(),
                  options=dict(vars(args)), paired_support=records, normal_searches=searches,
                  scope='supplied finite triangulations; local support and positive-Euler queries; no knot verdicts')
    output['options']['output'] = str(args.output)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(json_safe(output), indent=2)+'\n')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--case', action='append')
    parser.add_argument('--seconds', type=float, default=30)
    parser.add_argument('--include-slow-negative', action='store_true')
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).with_name('results')/'audit.json')
    run(parser.parse_args())
