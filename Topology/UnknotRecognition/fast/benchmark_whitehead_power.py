"""Matched historical controls for compressed Whitehead power minimization."""
import argparse
from contextlib import ExitStack
import json
from pathlib import Path
import platform
import random
from statistics import median
import subprocess
import sys
from time import perf_counter, process_time
from types import ModuleType
from unittest.mock import patch

from benchmark_compressed_words import cases
from fastunknot import Diagram, recognize, compressed_search, compressed_group, group_certificate
from fastunknot.compressed_words import WordArena, CompressedLimit

BASELINE = '6773a9b6e2ab50cdae07a627397054ce4a522b6d'


def historical(name):
    path = f'Topology/UnknotRecognition/fast/fastunknot/{name}.py'
    source = subprocess.check_output(['git', 'show', f'{BASELINE}:{path}'], text=True)
    module = ModuleType(f'fastunknot.recorded_{name}')
    module.__package__ = 'fastunknot'
    exec(compile(source, f'{BASELINE}:{path}', 'exec'), module.__dict__)
    return module


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--case', action='append', choices=[name for name, _ in cases()])
    parser.add_argument('--rounds', type=int, default=5)
    parser.add_argument('--queries-only', action='store_true')
    args = parser.parse_args()
    if args.rounds < 1:
        parser.error('--rounds must be positive')
    old_search, old_group, old_replay = [historical(x) for x in
        ('compressed_search', 'group_certificate', 'compressed_group')]
    current = group_certificate.group_decide
    rng, rows = random.Random(2700), []
    for name, diagram in cases():
        if args.case and name not in args.case:
            continue
        samples = []
        for repetition in range(args.rounds+1):
            order, measurements = ['baseline', 'control', 'powers'], {}
            rng.shuffle(order)
            for arm in order:
                with ExitStack() as stack:
                    if arm != 'powers':
                        stack.enter_context(patch.object(compressed_search, '_search', old_search._search))
                        stack.enter_context(patch.object(compressed_group, 'verify_moves', old_replay.verify_moves))
                        stack.enter_context(patch.object(group_certificate, 'group_decide', old_group.group_decide))
                    start, cpu_start = perf_counter(), process_time()
                    result = recognize(Diagram.from_pd(diagram.pd), use_group=True,
                        group_compressed_search=True, group_relators=True,
                        group_seconds=15, group_max_work=20000000, seconds=18, max_objects=50000)
                    group = result.evidence.get('group', {})
                    measurements[arm] = dict(seconds=perf_counter()-start, cpu_seconds=process_time()-cpu_start, status=result.status,
                        method=result.method, search_stats=group.get('search_stats'))
                    assert result.status == 'UNKNOT'
            if repetition:
                samples.append(dict(order=order, measurements=measurements))
        rows.append(dict(name=name, pd=diagram.pd, samples=samples,
            median_seconds={a: median(s['measurements'][a]['seconds'] for s in samples) for a in order}))
        print(name, rows[-1]['median_seconds'], flush=True)
    capacity = []
    diagram = dict(cases())['gordian']
    for cap in (() if args.queries_only else (4096, 8192)):
        samples = []
        for repetition in range(args.rounds+1):
            order, measurements = ['baseline', 'control', 'powers'], {}
            rng.shuffle(order)
            for arm in order:
                with ExitStack() as stack:
                    decide = current
                    if arm != 'powers':
                        stack.enter_context(patch.object(compressed_search, '_search', old_search._search))
                        stack.enter_context(patch.object(compressed_group, 'verify_moves', old_replay.verify_moves))
                        decide = old_group.group_decide
                    start = perf_counter()
                    result = decide(Diagram.from_pd(diagram.pd), seconds=15, max_letters=cap,
                        max_work=20000000, adaptive_search=True, relator_moves=True)
                    measurements[arm] = dict(seconds=perf_counter()-start, status=result['status'],
                        moves=len(result.get('certificate', {}).get('moves', [])), search_stats=result['search_stats'])
                    assert result['status'] == 'UNKNOT'
            if repetition:
                samples.append(dict(order=order, measurements=measurements))
        capacity.append(dict(max_letters=cap, samples=samples))
        print('capacity', cap, {a: median(s['measurements'][a]['seconds'] for s in samples) for a in order}, flush=True)
    kernels = []
    for bits in (() if args.queries_only else (4, 8, 12, 100, 500)):
        samples = []
        for repetition in range(args.rounds+1):
            order, measurements = ['baseline', 'control', 'powers'], {}
            rng.shuffle(order)
            for arm in order:
                start, arena = perf_counter(), WordArena(max_work=1000000)
                n = 2**bits
                base = arena.concat(arena.letter(1), arena.power(arena.letter(2), n))
                roots = [arena.power(base, 2), arena.power(base, 3)]
                moves, alive, reason = [], {1, 2}, None
                try:
                    success = (compressed_search._search if arm == 'powers' else old_search._search)(
                        arena, roots, alive, moves, relator_moves=True, max_letters=5)
                except CompressedLimit as exc:
                    success, reason = False, str(exc)
                measurements[arm] = dict(seconds=perf_counter()-start, success=success, reason=reason,
                    moves=len(moves), nodes=len(arena.rules)-1, stats=arena.stats.copy())
            if repetition:
                samples.append(dict(order=order, measurements=measurements))
        kernels.append(dict(bits=bits, samples=samples))
        print('kernel', bits, {a: (measurements[a]['success'], measurements[a]['moves'],
            median(s['measurements'][a]['seconds'] for s in samples)) for a in order}, flush=True)
    args.output.write_text(json.dumps(dict(python=sys.version, platform=platform.platform(),
        baseline_commit=BASELINE, seed=2700, measured_rounds=args.rounds, excluded_warmups=1,
        max_work=20000000, kernel_max_work=1000000, max_nodes=100000,
        query_scope='Fresh PD construction and whole recognition with compressed search and independent replay',
        capacity_scope='Fresh PD construction and adaptive group search plus independent replay, Gordian at matched letter caps',
        kernel_scope='Full construction and simplification of a supplied abstract Z presentation, not a knot diagram',
        censoring='Failed bounded search is censored; never treat it as completed recognition or form completion speedups',
        rows=rows, capacity=capacity, kernels=kernels), indent=2)+'\n')


if __name__ == '__main__':
    main()
