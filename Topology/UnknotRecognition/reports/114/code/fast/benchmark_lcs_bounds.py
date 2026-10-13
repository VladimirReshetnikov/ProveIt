"""Ablation of signed-alphabet run bounds and incremental LCS witnesses."""
import argparse
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
from fastunknot import Diagram, recognize, compressed_lcs
from fastunknot.compressed_words import WordArena, CompressedLimit
from fastunknot.compressed_overlap import whole_donor_move, cyclic_overlap_move, apply_cyclic_overlap

BASELINE = 'e678ef097b89d89e637b50241b14dcd7aa618373'
Current = compressed_lcs.CommonSubstring


class BoundsOnly(Current):
    def extensions(self, u, v):
        # Retain the previous eager materialization after computing bounds.
        return iter(list(super().extensions(u, v)))


class IncrementalOnly(Current):
    def shared_runs(self, nodes, common):
        # Original length bound, with the new incremental witness loop.
        return self.arena.lengths


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    old = historical('compressed_lcs', BASELINE).CommonSubstring
    factories = {'baseline': old, 'control': old, 'bounds-only': BoundsOnly,
                 'incremental-only': IncrementalOnly, 'full': Current}
    rng, rows = random.Random(2910), []
    for name, diagram in cases():
        samples = []
        for repetition in range(6):
            order, measurements = ['baseline', 'control', 'full'], {}
            rng.shuffle(order)
            for arm in order:
                with patch.object(compressed_lcs, 'CommonSubstring', factories[arm]):
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
            assert len({r['certificate_sha256'] for r in measurements.values()}) == 1
            if repetition:
                samples.append(dict(order=order, measurements=measurements))
        rows.append(dict(name=name, pd=diagram.pd, samples=samples,
            median_seconds={a: median(s['measurements'][a]['seconds'] for s in samples) for a in order}))
        print(name, rows[-1]['median_seconds'], flush=True)
    kernels = []
    for family in ('repeated', 'interior', 'same-alphabet'):
        for bits in (8, 32, 500):
            samples = []
            for repetition in range(6):
                order, measurements = list(factories), {}
                rng.shuffle(order)
                for arm in order:
                    start = perf_counter()
                    arena, n = WordArena(max_work=2000000), 2**bits
                    if family == 'repeated':
                        run = arena.power(arena.letter(1), n)
                        u = arena.concat(run, arena.from_word([2, 2]))
                        v = arena.concat(run, arena.from_word([3, 3]))
                        x, y = arena.concat(u, u), arena.concat(v, v)
                        expected = n
                    elif family == 'interior':
                        half = arena.power(arena.letter(1), n//2)
                        x = arena.concat(arena.concat(arena.letter(2), half), arena.concat(half, arena.letter(2)))
                        y = arena.concat(arena.concat(arena.letter(3), half), arena.concat(half, arena.letter(3)))
                        expected = n
                    else:
                        run = arena.power(arena.from_word([1, 2]), n)
                        x, y = arena.concat(run, arena.from_word([1, 3])), arena.concat(run, arena.from_word([3, 1]))
                        expected = 2*n
                    try:
                        answer = factories[arm](arena).longest(x, y)
                        assert answer[0] == expected
                        status, reason = 'COMPLETE', None
                    except CompressedLimit as exc:
                        answer, status, reason = None, 'LIMIT', str(exc)
                    measurements[arm] = dict(seconds=perf_counter()-start, status=status, reason=reason,
                        answer=answer, nodes=len(arena.rules)-1, stats=arena.stats.copy())
                if repetition:
                    samples.append(dict(order=order, measurements=measurements))
            kernels.append(dict(family=family, bits=bits, samples=samples))
            print(family, bits, {a: (measurements[a]['status'],
                median(s['measurements'][a]['seconds'] for s in samples)) for a in order}, flush=True)
    moves = []
    for bits in (8, 32, 500):
        samples = []
        for repetition in range(6):
            order, measurements = ['baseline', 'control', 'full'], {}
            rng.shuffle(order)
            for arm in order:
                start = perf_counter()
                arena, n = WordArena(max_work=2000000), 2**bits
                long_run = arena.power(arena.letter(1), n)
                short_run = arena.power(arena.letter(1), n//4)
                roots = []
                for g in (2, 3):
                    gap = arena.from_word([g, g])
                    roots.append(arena.concat(arena.concat(long_run, gap), arena.concat(short_run, gap)))
                try:
                    with patch.object(compressed_lcs, 'CommonSubstring', factories[arm]):
                        assert whole_donor_move(arena, roots) is None
                        move = cyclic_overlap_move(arena, roots)
                        assert move is not None and move['overlap'] == n
                        apply_cyclic_overlap(arena, roots, move)
                    assert sum(arena.lengths[r] for r in roots) == n+3*(n//4)+12
                    status, reason = 'COMPLETE', None
                except CompressedLimit as exc:
                    move, status, reason = None, 'LIMIT', str(exc)
                measurements[arm] = dict(seconds=perf_counter()-start, status=status, reason=reason,
                    move=move, nodes=len(arena.rules)-1, stats=arena.stats.copy())
            if repetition:
                samples.append(dict(order=order, measurements=measurements))
        moves.append(dict(bits=bits, samples=samples))
        print('move', bits, {a:(measurements[a]['status'],
            median(s['measurements'][a]['seconds'] for s in samples)) for a in order}, flush=True)
    args.output.write_text(json.dumps(dict(python=sys.version, platform=platform.platform(),
        baseline_commit=BASELINE, seed=2910, measured_rounds=5, excluded_warmups=1,
        max_work=20000000, kernel_max_work=2000000, max_nodes=100000,
        comparison='Archived LCS class in the common current recognition and replay harness',
        arms={'baseline': 'archived matcher', 'control': 'identical baseline',
              'bounds-only': 'shared-run bounds, eager witness collection',
              'incremental-only': 'incremental witnesses with original word-length bounds',
              'full': 'shared-run bounds and incremental witnesses'},
        query_scope='Fresh PD, full recognition and independent replay; digest outside timer',
        kernel_scope='Grammar construction and exact uncapped LCS; LIMIT is censored, never a negative result',
        move_scope='Grammar construction, failed whole-donor search, cyclic query and checked application; not a knot verdict',
        rows=rows, kernels=kernels, moves=moves), indent=2)+'\n')


if __name__ == '__main__':
    main()
