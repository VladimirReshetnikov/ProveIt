"""Focused controls for uniform-metadata reuse in donor pair filtering."""
import argparse
import json
from pathlib import Path
import platform
import random
from statistics import median
import sys
from time import perf_counter
from unittest.mock import patch
from benchmark_whitehead_power import historical
from fastunknot import compressed_search, compressed_overlap
from fastunknot.compressed_words import WordArena

BASELINE = '87e9585ec4761af5e7986d6f0e44bcb940d8ec78'
FILTERED = '3e9afde43cea128dcbbb3ee375a9a18d7f272d06'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    old = historical('compressed_overlap', BASELINE).whole_donor_move
    filtered = historical('compressed_overlap', FILTERED).whole_donor_move
    current = compressed_overlap.whole_donor_move
    rng, rows = random.Random(3011), []
    for family, bits in [('quotient', h) for h in (8, 32, 500)]+[('partial', 500)]:
        factories = ({'baseline': old, 'control': old, 'filtered': filtered, 'shortcut': current}
                     if family == 'quotient' else {'filtered': filtered, 'control': filtered, 'shortcut': current})
        samples = []
        for repetition in range(22):
            order, measurements = list(factories), {}
            rng.shuffle(order)
            for arm in order:
                with patch.object(compressed_overlap, 'whole_donor_move', factories[arm]):
                    start = perf_counter()
                    arena, n = WordArena(max_work=2000000), 2**bits
                    if family == 'quotient':
                        roots = [arena.power(arena.letter(1), n), arena.power(arena.letter(1), n*n+1)]
                        moves = []
                        assert compressed_search._search(arena, roots, {1, 2}, moves, relator_moves=True, max_letters=0)
                        assert len(moves) == 2
                    else:
                        run = arena.power(arena.from_word([1, 2]), n)
                        roots = [arena.concat(run, arena.from_word([1, 3])), arena.concat(run, arena.from_word([3, 1]))]
                        assert compressed_overlap.whole_donor_move(arena, roots) is None
                        move = compressed_overlap.cyclic_overlap_move(arena, roots)
                        assert move['overlap'] == 2*n
                        compressed_overlap.apply_cyclic_overlap(arena, roots, move)
                        assert sum(arena.lengths[r] for r in roots) == 2*n+6
                        moves = [move]
                    measurements[arm] = dict(seconds=perf_counter()-start, moves=moves,
                        nodes=len(arena.rules)-1, stats=arena.stats.copy())
            assert len({json.dumps(m['moves'], sort_keys=True) for m in measurements.values()}) == 1
            if repetition:
                samples.append(dict(order=order, measurements=measurements))
        row = dict(family=family, bits=bits, samples=samples,
            median_seconds={a:median(s['measurements'][a]['seconds'] for s in samples) for a in order})
        rows.append(row)
        print(family, bits, row['median_seconds'], flush=True)
    args.output.write_text(json.dumps(dict(python=sys.version, platform=platform.platform(),
        baseline_commit=BASELINE, filtered_commit=FILTERED, seed=3011,
        measured_rounds=21, excluded_warmups=1, max_work=2000000, max_nodes=100000,
        scope='Construction and abstract quotient search or complete local partial-move operation; all traces identical across arms',
        comparison='Archived donor helpers in the common current search, matcher and word arena; no knot-verdict claim',
        rows=rows), indent=2)+'\n')


if __name__ == '__main__':
    main()
