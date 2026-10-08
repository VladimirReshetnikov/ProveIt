"""Historical controls for compressed donor deletion and exact pattern matching."""
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
from fastunknot.compressed_match import MatchTable, first_occurrence
from fastunknot.compressed_words import WordArena, CompressedLimit
from fastunknot.group_certificate import group_decide

BASELINE = '59054ec761d10179910648bc7122b9bc16ebf075'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    old = historical('compressed_search', BASELINE)
    current, rng, rows = compressed_search._search, random.Random(2705), []
    for name, diagram in cases():
        samples = []
        for repetition in range(6):
            order, measurements = ['baseline', 'control', 'matching'], {}
            rng.shuffle(order)
            for arm in order:
                with patch.object(compressed_search, '_search', current if arm == 'matching' else old._search):
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
            order, measurements = ['baseline', 'control', 'matching'], {}
            rng.shuffle(order)
            for arm in order:
                with patch.object(compressed_search, '_search', current if arm == 'matching' else old._search):
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
    presentations = []
    for bits in (8, 32, 100, 500):
        samples = []
        for repetition in range(6):
            order, measurements = ['baseline', 'control', 'matching'], {}
            rng.shuffle(order)
            for arm in order:
                start, arena = perf_counter(), WordArena(max_work=20000000)
                donor = arena.power(arena.letter(1), 2**bits)
                target = arena.concat(arena.letter(2), arena.concat(donor, arena.from_word([-2, 1])))
                roots, moves, reason = [donor, target], [], None
                try:
                    success = (current if arm == 'matching' else old._search)(arena, roots, {1, 2},
                        moves, relator_moves=True, max_letters=4)
                    if not success:
                        reason = 'stalled'
                except CompressedLimit as exc:
                    success, reason = False, str(exc)
                measurements[arm] = dict(seconds=perf_counter()-start, success=success, reason=reason,
                    moves=len(moves), nodes=len(arena.rules)-1, stats=arena.stats.copy())
            if repetition:
                samples.append(dict(order=order, measurements=measurements))
        presentations.append(dict(bits=bits, samples=samples))
        print('presentation', bits, {a: (measurements[a]['success'], measurements[a]['moves'],
            median(s['measurements'][a]['seconds'] for s in samples)) for a in order}, flush=True)
    matching = []
    for bits in (8, 32, 64):
        for kind in ('first-hit', 'later-hit', 'absent'):
            samples = []
            for repetition in range(6):
                order, measurements = ['table', 'adaptive', 'control'], {}
                rng.shuffle(order)
                for arm in order:
                    start, arena = perf_counter(), WordArena(max_work=20000000)
                    n = 2**bits
                    pattern = arena.power(arena.from_word([1, 2]), n)
                    if kind == 'first-hit':
                        text = arena.concat(arena.letter(3), arena.concat(pattern, arena.letter(3)))
                        expected = 1
                    elif kind == 'later-hit':
                        text = arena.concat(arena.from_word([1, 3]), arena.concat(
                            arena.power(arena.letter(3), n), pattern))
                        expected = n+2
                    else:
                        text = arena.concat(arena.from_word([1, 3]), arena.concat(
                            arena.power(arena.from_word([1, 2]), n-1), arena.from_word([1, 3])))
                        expected = None
                    try:
                        position = (MatchTable(arena, pattern, text).first() if arm == 'table'
                                    else first_occurrence(arena, pattern, text))
                        assert position == expected
                        status = 'COMPLETE'
                    except CompressedLimit:
                        position, status = None, 'INCONCLUSIVE'
                    measurements[arm] = dict(seconds=perf_counter()-start, status=status,
                        position=position, expected=expected, nodes=len(arena.rules)-1, stats=arena.stats.copy())
                if repetition:
                    samples.append(dict(order=order, measurements=measurements))
            matching.append(dict(bits=bits, kind=kind, samples=samples))
            print('matching', bits, kind, {a: (measurements[a]['status'],
                median(s['measurements'][a]['seconds'] for s in samples)) for a in order}, flush=True)
    args.output.write_text(json.dumps(dict(python=sys.version, platform=platform.platform(),
        baseline_commit=BASELINE, seed=2705, measured_rounds=5, excluded_warmups=1,
        max_work=20000000, max_nodes=100000, group_seconds=15, global_seconds=18,
        query_scope='Fresh PD and whole recognition with independent replay; historical identical-search controls',
        capacity_scope='Fresh PD and adaptive group search with independent replay at matched Gordian letter caps',
        presentation_scope='Full construction and search on an abstract supplied presentation, not a knot verdict',
        matching_scope='Full grammar construction and exact first substring query; table vs first-letter probe plus table fallback',
        censoring='Stalls and limits are incomplete searches; never form completion speedups against them',
        rows=rows, capacity=capacity, presentations=presentations, matching=matching), indent=2)+'\n')


if __name__ == '__main__':
    main()
