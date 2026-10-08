#!/usr/bin/env python3
"""Paired raw-scanner comparison. Run from any directory; Python stdlib only.

The package layout is benchmarks/ beside fast/. The second path below supports
running the same script from the development workspace before packaging.
All scanners receive exactly the same initial order. The optional DP backend
pays for its optimization inside its per-call time budget and reported time.
No simplification, Seifert/Alexander/Jones filter, or visible-sum factorization
is used. Thus the measurements isolate the raw exact/decision backends.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import random
import statistics
import sys
import time
from datetime import datetime, timezone

HERE = Path(__file__).resolve().parent
FAST = HERE.parent / 'fast'
if not FAST.is_dir():
    FAST = HERE.parent.parent / 'fast'
sys.path.insert(0, str(FAST))
from fastunknot import Diagram, khovanov_rank
from fastunknot.barcode_scan import BarcodeScan
from fastunknot.component_scan import ComponentScan, compressed_khovanov_rank
from fastunknot.geometry import ScanLimit
from fastunknot.ordering import best_scan_order, order_profile
from fastunknot.order_dp import improve_scan_order
from fastunknot.scalar_split import FittingScan, fitting_khovanov_rank, fitting_khovanov_decide

BACKENDS = ['standard', 'component', 'fitting_exact', 'fitting_decision', 'fitting_decision_dp']
RANDOM_SEED = 54287
NAMED = ['hard_unknot_8', 'conway', 'kinoshita_terasaka', 'conway_sum_2',
         'conway_sum_3', 'conway_sum_8', 'stress_braid5_36']


def corpus(random_count):
    for name in NAMED:
        data = json.loads((FAST / 'examples' / (name + '.json')).read_text())
        yield name, Diagram.from_json(data), dict(kind='named', input=data)
    for strands, p in [(3, 11), (4, 9), (5, 8)]:
        word = list(range(1, strands)) * p
        yield f'torus_{strands}_{p}', Diagram.from_braid(strands, word), dict(
            kind='named', input=dict(braid=dict(strands=strands, word=word)))
    rng, count = random.Random(RANDOM_SEED), 0
    # First random_count valid closures constitute the unselected random set.
    # Number 24 is separately labeled: it was selected by the exploratory probe
    # for having a scalar split and is excluded from any random-frequency claim.
    while count < max(random_count, 24):
        strands = rng.randrange(3, 7)
        word = [rng.choice([-1, 1]) * rng.randrange(1, strands)
                for _ in range(rng.randrange(10, 25))]
        try:
            diagram = Diagram.from_braid(strands, word)
        except ValueError:
            continue
        count += 1
        if count <= random_count or count == 24:
            kind = 'random_unselected' if count <= random_count else 'selected_split_example'
            yield f'random_{count}', diagram, dict(kind=kind, valid_index=count,
                input=dict(braid=dict(strands=strands, word=word)))


def source_hashes():
    names = ['scan_fast.py', 'component_scan.py', 'barcode_scan.py', 'scalar_split.py', 'order_dp.py']
    return {name: hashlib.sha256((FAST / 'fastunknot' / name).read_bytes()).hexdigest() for name in names}


def one_run(backend, diagram, order, seconds, max_objects):
    started = time.perf_counter()
    result, dp = None, None
    actual_order = order
    try:
        if backend == 'fitting_decision_dp':
            dp_started = time.perf_counter()
            dp_result = improve_scan_order(diagram.pd, order=order, window=10, passes=2,
                                            objective='mass', seconds=seconds)
            actual_order = dp_result['order']
            dp = {key: dp_result[key] for key in ['order', 'initial_score', 'score', 'complete', 'objective']}
            dp['seconds'] = time.perf_counter() - dp_started
        remaining = max(0.0, seconds - (time.perf_counter() - started))
        options = dict(order=actual_order, seconds=remaining, max_objects=max_objects)
        if backend == 'standard':
            result = khovanov_rank(diagram.pd, **options)
        elif backend == 'component':
            result = compressed_khovanov_rank(diagram.pd, **options)
        elif backend == 'fitting_exact':
            result = fitting_khovanov_rank(diagram.pd, **options)
        else:
            result = fitting_khovanov_decide(diagram.pd, **options)
        row = dict(outcome='completed', seconds=time.perf_counter() - started,
                   result={k: result[k] for k in ['rank', 'reduced_rank', 'by_degree', 'rank_capped', 'status'] if k in result},
                   stats=result['stats'], stage_history=result.get('stages', []))
    except ScanLimit as error:
        row = dict(outcome='resource_limit', reason=str(error), seconds=time.perf_counter() - started)
    if dp is not None:
        row['dp'] = dp
        row['scan_seconds'] = row['seconds'] - dp['seconds']
    return row


def summarize(runs, order_seconds):
    out = {}
    for backend in BACKENDS:
        completed = [row for row in runs if row['backend'] == backend and row['outcome'] == 'completed']
        failed = [row for row in runs if row['backend'] == backend and row['outcome'] != 'completed']
        data = dict(completed=len(completed), limited=len(failed))
        if completed:
            times = [row['seconds'] for row in completed]
            data.update(median_seconds=statistics.median(times), min_seconds=min(times), max_seconds=max(times),
                        median_with_initial_order=statistics.median(times) + order_seconds,
                        result=completed[0]['result'], stats=completed[0]['stats'],
                        stage_history=completed[0]['stage_history'])
            if 'dp' in completed[0]:
                data['dp'] = dict(completed[0]['dp'], seconds=statistics.median(row['dp']['seconds'] for row in completed))
                data['median_scan_seconds'] = statistics.median(row['scan_seconds'] for row in completed)
        out[backend] = data
    exact_ranks = {data['result']['rank'] for data in out.values()
                   if data.get('completed') and 'rank' in data['result']}
    if len(exact_ranks) > 1:
        raise ArithmeticError('exact backends disagreed')
    if exact_ranks:
        expected = min(3, next(iter(exact_ranks)))
        for data in out.values():
            if data.get('completed') and 'rank_capped' in data['result']:
                if data['result']['rank_capped'] != expected:
                    raise ArithmeticError('a capped decision disagreed with exact rank')
    return out


def synthetic_case(kind, copies, layers=8, *, decision=False):
    cl = FittingScan if kind == 'mixed' else BarcodeScan
    options = dict(shape_cache=False)
    if decision:
        options.update(rank_cap=3, length_cap=2)
    scan = cl(**options)
    a = scan.algebra.intern(((0, 1), (2, 3)))
    b = scan.algebra.intern(((0, 3), (1, 2)))
    scan.points = frozenset(range(4))
    if kind == 'mixed':
        scan.mid = [m for _ in range(copies) for m in (a, a, b)]
        scan.deg = [h for _ in range(copies) for h in (0, 1, 1)]
        scan.out = [{} for _ in scan.mid]
        for j in range(copies):
            for i in range(j + 1):
                scan.out[3 * j][3 * i + 1] = 2
                scan.out[3 * j][3 * i + 2] = 1
    else:
        scan.mid = [a] * (copies * layers)
        scan.deg = [h for h in range(layers) for _ in range(copies)]
        scan.out = [{} for _ in scan.mid]
        for h in range(layers - 1):
            for i in range(copies):
                scan.out[h * copies + i][(h + 1) * copies + i] = 2
                if i + 1 < copies:
                    scan.out[h * copies + i][(h + 1) * copies + i + 1] = 2
    scan.inc = [set() for _ in scan.mid]
    for source, row in enumerate(scan.out):
        for target in row:
            scan.inc[target].add(source)
    scan.live = len(scan.mid)
    scan.owner, scan.weights = [0] * scan.live, [{0: 1}]
    before = scan.live
    started = time.perf_counter()
    scan._compress([0] * scan.live)
    seconds = time.perf_counter() - started
    scan.check_d_squared()
    return dict(kind=kind, copies=copies, layers=layers if kind == 'pure' else 2,
                decision=decision, before_objects=before, after_objects=scan.live,
                weights=scan.weights, seconds=seconds, stats=scan.stats)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=HERE / 'paired_results.json')
    parser.add_argument('--repeats', type=int, default=3)
    parser.add_argument('--seconds', type=float, default=3.0)
    parser.add_argument('--max-objects', type=int, default=50000)
    parser.add_argument('--random-count', type=int, default=8)
    args = parser.parse_args()
    if args.repeats < 1 or args.seconds <= 0 or args.max_objects < 1 or args.random_count < 0:
        parser.error('invalid benchmark bounds')
    start_hashes = source_hashes()
    result = dict(environment=dict(utc=datetime.now(timezone.utc).isoformat(), python=sys.version,
        platform=platform.platform(), processor=platform.processor(), cpu_count=os.cpu_count(),
        load_average_start=list(os.getloadavg()) if hasattr(os, 'getloadavg') else None),
        configuration=dict(repeats=args.repeats, seconds_per_call=args.seconds,
            max_physical_objects=args.max_objects, random_seed=RANDOM_SEED,
            random_count=args.random_count, fitting_max_objects=48, fitting_max_variables=1024,
            fitting_max_splits=16, fitting_basis_trials=64, fitting_combination_trials=16,
            fitting_cache_entries=4096, length_cap=2, dp_window=10, dp_passes=2,
            initial_order='best greedy from at most twelve starting crossings',
            timing='3 interleaved repetitions; median; DP preprocessing is included; no filters'),
        source_sha256=start_hashes, cases=[])
    # Import/init warmup is separate from measured work and uses a tiny knot.
    warmup = Diagram.from_braid(2, [1, 1, 1])
    for backend in BACKENDS:
        one_run(backend, warmup, [0, 1, 2], args.seconds, args.max_objects)
    for index, (name, diagram, metadata) in enumerate(corpus(args.random_count)):
        started = time.perf_counter()
        order = best_scan_order(diagram.pd, tries=min(len(diagram.pd), 12))
        order_seconds = time.perf_counter() - started
        row = dict(name=name, crossings=len(diagram.pd), pd=diagram.pd, order=order,
                   order_profile=order_profile(diagram.pd, order), initial_order_seconds=order_seconds,
                   **metadata, runs=[])
        for repeat in range(args.repeats):
            offset = (index + repeat) % len(BACKENDS)
            sequence = BACKENDS[offset:] + BACKENDS[:offset]
            for backend in sequence:
                run = one_run(backend, diagram, order, args.seconds, args.max_objects)
                run.update(backend=backend, repetition=repeat)
                row['runs'].append(run)
        row['summary'] = summarize(row['runs'], order_seconds)
        result['cases'].append(row)
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(result, indent=2) + '\n')
        print(name, {b: round(v['median_seconds'], 6) if v.get('completed') else 'LIMIT'
                     for b, v in row['summary'].items()}, flush=True)
    result['synthetic'] = [synthetic_case('pure', q, decision=decision)
        for q in [2, 8, 32, 128] for decision in [False, True]]
    result['synthetic'] += [synthetic_case('mixed', q) for q in [2, 4, 8, 16]]
    result['source_sha256_end'] = source_hashes()
    result['source_unchanged_during_run'] = result['source_sha256_end'] == start_hashes
    result['environment']['load_average_end'] = list(os.getloadavg()) if hasattr(os, 'getloadavg') else None
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    # Emit a concrete actual-diagram certificate outside the timed sample.
    diagram = Diagram.from_json(json.loads((FAST / 'examples' / 'conway.json').read_text()))
    witnessed = fitting_khovanov_rank(diagram.pd, record_witnesses=True)
    certificate = dict(name='conway', pd=diagram.pd, order=witnessed['order'], rank=witnessed['rank'],
                       witnesses=witnessed['witnesses'])
    args.output.with_name('conway_fitting_witnesses.json').write_text(json.dumps(certificate, indent=2) + '\n')
    print('Wrote', args.output, flush=True)

if __name__ == '__main__':
    main()
