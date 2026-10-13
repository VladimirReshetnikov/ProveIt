"""Component-controlled audit of quotient deletion and uniform-word summaries."""
import argparse
from contextlib import contextmanager, ExitStack
import hashlib
import json
from pathlib import Path
import platform
import random
from statistics import median
import sys
from time import perf_counter
from unittest.mock import patch

from benchmark_compressed_words import cases
from benchmark_whitehead_power import historical
from benchmark_indexed_equality import baseline_arena
from fastunknot import Diagram, recognize, compressed_search, compressed_group, compressed_overlap
from fastunknot.compressed_words import WordArena, CompressedLimit
from fastunknot.group_certificate import group_decide

BASELINE = '10bc9bb75405f1cd22d82158c04a06c31d0fcc3d'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    old_arena, old_overlap = baseline_arena(BASELINE), historical('compressed_overlap', BASELINE)
    old_limit = old_arena.tick.__globals__['CompressedLimit']
    new_move, new_apply = compressed_overlap.whole_donor_move, compressed_overlap.apply_whole_donor
    rng = random.Random(2709)

    @contextmanager
    def environment(arm):
        factory = WordArena if arm in ('uniform', 'full') else old_arena
        move, apply = ((new_move, new_apply) if arm in ('quotient-prune', 'full') else
                       (old_overlap.whole_donor_move, old_overlap.apply_whole_donor))
        with ExitStack() as stack:
            stack.enter_context(patch.object(compressed_search, 'WordArena', factory))
            stack.enter_context(patch.object(compressed_group, 'WordArena', factory))
            stack.enter_context(patch.object(compressed_overlap, 'whole_donor_move', move))
            stack.enter_context(patch.object(compressed_overlap, 'apply_whole_donor', apply))
            yield factory

    rows = []
    for name, diagram in cases():
        samples = []
        for repetition in range(6):
            order, measurements = ['baseline', 'control', 'full'], {}
            rng.shuffle(order)
            for arm in order:
                with environment(arm):
                    start = perf_counter()
                    result = recognize(Diagram.from_pd(diagram.pd), use_group=True,
                        group_compressed_search=True, group_relators=True,
                        group_seconds=15, group_max_work=20000000, seconds=18, max_objects=50000)
                    elapsed = perf_counter()-start
                group = result.evidence.get('group', {})
                measurements[arm] = dict(seconds=elapsed, status=result.status, method=result.method,
                    search_stats=group.get('search_stats'), certificate_sha256=hashlib.sha256(
                        json.dumps(group.get('certificate'), sort_keys=True).encode()).hexdigest())
                assert result.status == 'UNKNOT'
            assert len({v['certificate_sha256'] for v in measurements.values()}) == 1
            if repetition:
                samples.append(dict(order=order, measurements=measurements))
        rows.append(dict(name=name, pd=diagram.pd, samples=samples,
            median_seconds={a: median(s['measurements'][a]['seconds'] for s in samples) for a in order}))
        print(name, rows[-1]['median_seconds'], flush=True)
    capacity = []
    diagram = dict(cases())['gordian']
    for cap in (4096, 8192):
        samples = []
        for repetition in range(6):
            order, measurements = ['baseline', 'control', 'full'], {}
            rng.shuffle(order)
            for arm in order:
                with environment(arm):
                    start = perf_counter()
                    result = group_decide(Diagram.from_pd(diagram.pd), seconds=15,
                        max_letters=cap, max_work=20000000, adaptive_search=True, relator_moves=True)
                    measurements[arm] = dict(seconds=perf_counter()-start, status=result['status'],
                        moves=len(result.get('certificate', {}).get('moves', [])), search_stats=result['search_stats'])
                assert result['status'] == 'UNKNOT'
            if repetition:
                samples.append(dict(order=order, measurements=measurements))
        capacity.append(dict(max_letters=cap, samples=samples))
        print('capacity', cap, {a: median(s['measurements'][a]['seconds'] for s in samples) for a in order}, flush=True)
    kernels = []
    for family, bits in [('quotient', h) for h in (4, 8, 32, 100, 500)]+[('allocation', 500)]:
        samples = []
        node_cap = 600 if family == 'allocation' else 100000
        for repetition in range(6):
            order, measurements = ['baseline', 'control', 'quotient-prune', 'uniform', 'full'], {}
            rng.shuffle(order)
            for arm in order:
                with environment(arm) as factory:
                    start = perf_counter()
                    arena, n = factory(max_work=1000000, max_nodes=node_cap), 2**bits
                    donor = arena.power(arena.letter(1), n)
                    target = (arena.power(arena.letter(1), n*n+1) if family == 'quotient' else
                              arena.concat(arena.letter(2), arena.concat(donor, arena.from_word([-2, 1]))))
                    roots, moves, reason = [donor, target], [], None
                    try:
                        success = compressed_search._search(arena, roots, {1, 2}, moves,
                            relator_moves=True, max_letters=4)
                        if not success:
                            reason = 'stalled'
                    except (CompressedLimit, old_limit) as exc:
                        success, reason = False, str(exc)
                    measurements[arm] = dict(seconds=perf_counter()-start, success=success, reason=reason,
                        moves=len(moves), nodes=len(arena.rules)-1, stats=arena.stats.copy())
                if arm == 'full':
                    assert success
            if repetition:
                samples.append(dict(order=order, measurements=measurements))
        kernels.append(dict(family=family, bits=bits, max_nodes=node_cap, samples=samples))
        print(family, bits, {a: (measurements[a]['success'], measurements[a]['moves'],
            median(s['measurements'][a]['seconds'] for s in samples)) for a in order}, flush=True)
    args.output.write_text(json.dumps(dict(python=sys.version, platform=platform.platform(),
        baseline_commit=BASELINE, seed=2709, measured_rounds=5, excluded_warmups=1,
        max_work=20000000, kernel_max_work=1000000, max_nodes=100000,
        group_seconds=15, global_seconds=18,
        comparison='Archived word kernel and donor helpers inside the common current recognition/replay harness',
        arms={'baseline': 'archived kernel and donor helpers', 'control': 'identical baseline',
              'quotient-prune': 'new quotient/pruning helpers, archived kernel',
              'uniform': 'new uniform kernel, archived one-copy helpers', 'full': 'both improvements'},
        query_scope='Fresh PD construction, full recognition and independent certificate replay',
        capacity_scope='Fresh PD and adaptive group search including replay at matched Gordian letter caps',
        kernel_scope='Full grammar construction and abstract presentation search; not knot-diagram verdicts',
        censoring='Resource exhaustion or stalling is incomplete search; never treat it as completion or form completion ratios',
        rows=rows, capacity=capacity, kernels=kernels), indent=2)+'\n')


if __name__ == '__main__':
    main()
