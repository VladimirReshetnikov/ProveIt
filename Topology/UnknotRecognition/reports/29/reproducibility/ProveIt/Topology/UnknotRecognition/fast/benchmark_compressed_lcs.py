"""Controlled recognition and exact compressed cyclic-overlap measurements."""
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
from fastunknot import Diagram, recognize, compressed_search
from fastunknot.compressed_lcs import CommonSubstring
from fastunknot.compressed_words import WordArena, CompressedLimit
from fastunknot.compressed_overlap import whole_donor_move, cyclic_overlap_move, apply_cyclic_overlap

BASELINE = '032ca00758df210d287f5a430708fe68065952d1'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    old = historical('compressed_search', BASELINE)._search
    current = compressed_search._search
    rng, rows = random.Random(2810), []
    for name, diagram in cases():
        samples = []
        for repetition in range(6):
            order, measurements = ['baseline', 'control', 'complete-overlap'], {}
            rng.shuffle(order)
            for arm in order:
                with patch.object(compressed_search, '_search', current if arm == 'complete-overlap' else old):
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
        row = dict(name=name, pd=diagram.pd, samples=samples,
            median_seconds={a: median(s['measurements'][a]['seconds'] for s in samples) for a in order})
        rows.append(row)
        print(name, row['median_seconds'], flush=True)
    kernels = []
    for family in ('cyclic', 'shifted'):
        for bits in (8, 16, 32, 100, 500):
            samples = []
            for repetition in range(6):
                order = ['full', 'bound', 'control'] if family == 'cyclic' else ['full', 'control']
                rng.shuffle(order)
                measurements = {}
                for arm in order:
                    start = perf_counter()
                    arena, n = WordArena(max_work=2000000), 2**bits
                    run = arena.power(arena.letter(1), n)
                    if family == 'cyclic':
                        x = arena.concat(run, arena.from_word([2, 2]))
                        y = arena.concat(run, arena.from_word([3, 3]))
                        x, y = arena.concat(x, x), arena.concat(y, y)
                    else:
                        x, y = arena.concat(run, arena.letter(2)), arena.concat(arena.letter(3), run)
                    try:
                        result = CommonSubstring(arena).longest(x, y,
                            n if family == 'cyclic' and arm != 'full' else None)
                        status, reason = 'COMPLETE', None
                        assert result[0] == n
                    except CompressedLimit as exc:
                        result, status, reason = None, 'LIMIT', str(exc)
                    measurements[arm] = dict(seconds=perf_counter()-start, status=status, reason=reason,
                        result=result, nodes=len(arena.rules)-1, stats=arena.stats.copy())
                if repetition:
                    samples.append(dict(order=order, measurements=measurements))
            kernels.append(dict(family=family, bits=bits, samples=samples))
            print(family, bits, {a: (measurements[a]['status'],
                median(s['measurements'][a]['seconds'] for s in samples)) for a in order}, flush=True)
    moves = []
    for bits in (8, 32, 100, 500):
        samples = []
        for repetition in range(6):
            start = perf_counter()
            arena, n = WordArena(max_work=2000000), 2**bits
            run = arena.power(arena.letter(1), n)
            roots = [arena.concat(run, arena.from_word([2, 2])), arena.concat(run, arena.from_word([3, 3]))]
            assert whole_donor_move(arena, roots) is None
            move = cyclic_overlap_move(arena, roots)
            assert move is not None and move['overlap'] == n
            apply_cyclic_overlap(arena, roots, move)
            elapsed = perf_counter()-start
            assert sum(arena.lengths[r] for r in roots) == n+6
            if repetition:
                samples.append(dict(seconds=elapsed, move=move, nodes=len(arena.rules)-1, stats=arena.stats.copy()))
        moves.append(dict(bits=bits, samples=samples))
        print('move', bits, median(s['seconds'] for s in samples), flush=True)
    args.output.write_text(json.dumps(dict(python=sys.version, platform=platform.platform(),
        baseline_commit=BASELINE, seed=2810, measured_rounds=5, excluded_warmups=1,
        max_work=20000000, kernel_max_work=2000000, max_nodes=100000,
        comparison='Archived search loop in the common current kernel, recognition and replay harness',
        query_scope='Fresh PD, full recognition, independent replay; digest checked outside clock',
        kernel_scope='Full grammar construction and exact LCS query; LIMIT is censored, never a negative result',
        cyclic_family='x=(a^N bb)^2,y=(a^N cc)^2; LCS=N; bound arm caps at proved shared-count upper bound N',
        shifted_family='x=a^N b,y=c a^N; LCS=N; full and control both use uncapped query',
        move_scope='Construction, failed whole-donor query, complete cyclic query and checked application; not a knot verdict',
        rows=rows, kernels=kernels, moves=moves), indent=2)+'\n')


if __name__ == '__main__':
    main()
