"""Matched audit of endpoint progressions certified by their two largest overlaps."""
import argparse
from contextlib import contextmanager
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
from fastunknot import Diagram, recognize, compressed_lcs, compressed_overlap, compressed_search
from fastunknot.compressed_words import WordArena, CompressedLimit

BASELINE = '8170a64c7e72b890972acf200812d6dc77ae436f'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    old_matcher = historical('compressed_lcs', BASELINE).CommonSubstring
    current_matcher = compressed_lcs.CommonSubstring
    rng, rows = random.Random(3015), []

    @contextmanager
    def environment(arm):
        matcher = current_matcher if arm == 'full' else old_matcher
        with patch.object(compressed_lcs, 'CommonSubstring', matcher):
            yield matcher

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
    kernels = []
    for family in ('prefix', 'interior', 'equal-bigrams', 'full-overlap', 'shifted-32', 'late-defect', 'markers-17', 'markers-64', 'markers-65', 'markers-power', 'broken-grid'):
        for bits in (8, 32, 500):
            samples = []
            for repetition in range(6):
                order, measurements = ['baseline', 'control', 'full'], {}
                rng.shuffle(order)
                for arm in order:
                    with environment(arm) as factory:
                        start = perf_counter()
                        arena, n = WordArena(max_work=2000000), 2**bits
                        if family.startswith('markers-'):
                            copies = n if family == 'markers-power' else int(family.split('-')[1])
                            run = arena.power(arena.from_word([1, 2]), n)
                            block = arena.concat(run, arena.letter(3))
                            x = y = arena.power(block, copies)
                        elif family == 'broken-grid':
                            block = arena.concat(arena.power(arena.from_word([1, 2]), n), arena.letter(3))
                            changed = arena.concat(arena.power(arena.from_word([2, 1]), n), arena.letter(3))
                            x = y = arena.concat(changed, arena.power(block, 64))
                        elif family == 'shifted-32':
                            block = list(range(1, 33))
                            x = arena.power(arena.from_word(block[7:]+block[:7]), n)
                            y = arena.power(arena.from_word(block), n)
                        elif family == 'late-defect':
                            run = arena.power(arena.from_word([1, 2]), n)
                            x = y = arena.concat(run, arena.letter(3))
                        elif family == 'full-overlap':
                            x = y = arena.power(arena.from_word([1, 2]), n)
                        elif family == 'interior':
                            half = arena.power(arena.from_word([1, 2]), n//2)
                            x = arena.concat(arena.concat(arena.letter(3), half), arena.concat(half, arena.letter(2)))
                            y = arena.concat(arena.concat(arena.letter(2), half), arena.concat(half, arena.letter(3)))
                        else:
                            run = arena.power(arena.from_word([1, 2]), n)
                            if family == 'prefix':
                                x, y = arena.concat(run, arena.from_word([1, 3])), arena.concat(run, arena.from_word([3, 1]))
                            else:
                                tail = arena.from_word([1, 1, 2, 2, 3, 3, 1, 3, 2, 1, 2, 3])
                                x = arena.concat(run, arena.concat(arena.letter(3), tail))
                                y = arena.concat(run, arena.concat(arena.letter(1), tail))
                        try:
                            if family.startswith('markers-'):
                                answer = factory(arena).overlaps(x, y)
                                assert sum(count for p, d, count in answer) == copies
                                end = 0
                                for first, step, count in sorted(answer):
                                    assert first == end+2*n+1
                                    assert step == (2*n+1 if count > 1 else 0)
                                    end = first+step*(count-1)
                                assert end == (2*n+1)*copies
                            elif family == 'broken-grid':
                                answer = factory(arena).overlaps(x, y)
                                assert answer == [(65*(2*n+1), 0, 1)]
                            elif family == 'shifted-32':
                                answer = factory(arena).overlaps(x, y)
                                assert sum(ap[2] for ap in answer) == n
                                assert all(p % 32 == 7 and (count == 1 or d == 32)
                                           for p, d, count in answer)
                                assert max(p+d*(count-1) for p, d, count in answer) == 32*n-25
                            elif family == 'late-defect':
                                answer = factory(arena).overlaps(x, y)
                                assert answer == [(2*n+1, 0, 1)]
                            elif family == 'full-overlap':
                                answer = factory(arena).overlaps(x, y)
                                assert sum(ap[2] for ap in answer) == n
                                assert all(p % 2 == 0 and (count == 1 or d == 2)
                                           for p, d, count in answer)
                                assert max(p+d*(count-1) for p, d, count in answer) == 2*n
                            else:
                                answer = factory(arena).longest(x, y)
                                assert answer[0] == 2*n
                            status, reason = 'COMPLETE', None
                        except CompressedLimit as exc:
                            answer, status, reason = None, 'LIMIT', str(exc)
                        measurements[arm] = dict(seconds=perf_counter()-start, status=status, reason=reason,
                            answer=answer, nodes=len(arena.rules)-1, stats=arena.stats.copy())
                if repetition:
                    samples.append(dict(order=order, measurements=measurements))
            kernels.append(dict(family=family, bits=bits, samples=samples))
            print(family, bits, {a:(measurements[a]['status'],
                median(s['measurements'][a]['seconds'] for s in samples)) for a in order}, flush=True)
    operations = []
    for family in ('partial', 'equal-bigrams-cyclic', 'quotient'):
        for bits in (8, 32, 500):
            samples = []
            for repetition in range(6):
                order = ['baseline', 'control', 'full']
                rng.shuffle(order)
                measurements = {}
                for arm in order:
                    with environment(arm):
                        start = perf_counter()
                        arena, n = WordArena(max_work=2000000), 2**bits
                        if family == 'equal-bigrams-cyclic':
                            run = arena.power(arena.from_word([1, 2]), n)
                            tail = arena.from_word([1, 1, 2, 2, 3, 3, 1, 3, 2, 1, 2, 3])
                            roots = [arena.concat(run, arena.concat(arena.letter(c), tail)) for c in (3, 1)]
                        elif family == 'partial':
                            run = arena.power(arena.from_word([1, 2]), n)
                            roots = [arena.concat(run, arena.from_word([1, 3])), arena.concat(run, arena.from_word([3, 1]))]
                        else:
                            roots = [arena.power(arena.letter(1), n), arena.power(arena.letter(1), n*n+1)]
                        moves = []
                        try:
                            if family in ('partial', 'equal-bigrams-cyclic'):
                                assert compressed_overlap.whole_donor_move(arena, roots) is None
                                move = compressed_overlap.cyclic_overlap_move(arena, roots)
                                assert move is not None and move['overlap'] == 2*n+(12 if family == 'equal-bigrams-cyclic' else 0)
                                compressed_overlap.apply_cyclic_overlap(arena, roots, move)
                                assert sum(arena.lengths[r] for r in roots) == 2*n+(15 if family == 'equal-bigrams-cyclic' else 6)
                                moves.append(move)
                            else:
                                assert compressed_search._search(arena, roots, {1, 2}, moves,
                                    relator_moves=True, max_letters=0)
                                assert len(moves) == 2
                            status, reason = 'COMPLETE', None
                        except CompressedLimit as exc:
                            status, reason = 'LIMIT', str(exc)
                        measurements[arm] = dict(seconds=perf_counter()-start, status=status, reason=reason,
                            moves=moves, nodes=len(arena.rules)-1, stats=arena.stats.copy())
                completed = [m['moves'] for m in measurements.values() if m['status'] == 'COMPLETE']
                assert all(m == completed[0] for m in completed)
                if repetition:
                    samples.append(dict(order=order, measurements=measurements))
            operations.append(dict(family=family, bits=bits, samples=samples))
            print(family, bits, {a:(measurements[a]['status'],
                median(s['measurements'][a]['seconds'] for s in samples)) for a in order}, flush=True)
    args.output.write_text(json.dumps(dict(python=sys.version, platform=platform.platform(),
        baseline_commit=BASELINE, seed=3015, measured_rounds=5, excluded_warmups=1,
        max_work=20000000, kernel_max_work=2000000, max_nodes=100000,
        comparison='Archived LCS class inside the common current word arena, donor, recognition and replay harness',
        query_scope='Fresh PD, full recognition and independent replay; digest outside clock',
        kernel_scope='Construction and exact LCS or complete overlaps; full-overlap expects all even lengths through 2*N, shifted-32 all lengths congruent to 7 mod 32 through 32*N, late-defect only the full word; markers-q expects exactly q multiples of 2*N+1, markers-power uses q=N, broken-grid only the full word',
        partial_scope='Construction, failed whole-donor search, cyclic partial query and checked application; not a knot verdict',
        quotient_scope='Construction and complete abstract pure-power search; controls assess successful whole-donor overhead',
        censoring='LIMIT is incomplete search, never a negative answer or completed-time denominator',
        rows=rows, kernels=kernels, operations=operations), indent=2)+'\n')


if __name__ == '__main__':
    main()
