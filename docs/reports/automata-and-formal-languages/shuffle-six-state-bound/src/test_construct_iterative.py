#!/usr/bin/env python3
"""Deterministic constructor and separation-suffix tests; not a coverage proof.
Python 3.10+, standard library only. Run from any working directory.
"""
from __future__ import annotations
from collections import Counter
import itertools
import json
import random
import time
from construct_iterative import construct, replay, step, validate_data, DEFAULT_DATA


def main() -> None:
    start = time.perf_counter()
    database = validate_data(DEFAULT_DATA)
    print(f"Python local certificate checks: {len(database)}", flush=True)
    count = 0
    kinds: Counter[str] = Counter()
    max_length = 0

    def check(m, n, cells, root=(0, 0)):
        nonlocal count, max_length
        word, reductions = construct(m, n, cells, database, root)
        states = replay(m, n, root, word)
        assert states[-1] == cells
        bound = len(cells) + min(len({i for i, _ in cells}), len({j for _, j in cells})) - 2
        assert len(word) <= bound
        count += 1
        max_length = max(max_length, len(word))
        kinds.update(d['kind'] for d in reductions)

    # Exhaustive, including all possible distinguished rows and columns.
    for m, n in [(1, 1), (1, 5), (2, 2), (2, 3), (2, 4), (2, 5), (3, 3), (3, 4)]:
        before = count
        universe = list(itertools.product(range(m), range(n)))
        for mask in range(1, 1 << (m*n)):
            cells = {p for k, p in enumerate(universe) if mask & (1 << k)}
            rs = {i for i, _ in cells}
            cs = {j for _, j in cells}
            for root in itertools.product(rs, cs):
                check(m, n, cells, root)
        print(f"Exhaustive {m}x{n}, all roots: {count-before} targets", flush=True)

    m = n = 4
    before = count
    universe = list(itertools.product(range(m), range(n)))
    for mask in range(1, 1 << 16):
        cells = {p for k, p in enumerate(universe) if mask & (1 << k)}
        if any(i == 0 for i, _ in cells) and any(j == 0 for _, j in cells):
            check(m, n, cells)
    print(f"Exhaustive 4x4, root (0,0): {count-before} targets", flush=True)

    rng = random.Random(20260920)
    before = count
    for d in rng.sample(list(database.values()), 240):
        m, n = d['m'], d['n']
        rows, cols = list(range(m)), list(range(n))
        rng.shuffle(rows); rng.shuffle(cols)
        cells = {(rows[i], cols[j]) for j, a in enumerate(d['columns'])
                 for i in range(m) if a & (1 << i)}
        check(m, n, cells, (rng.randrange(m), rng.randrange(n)))
    print(f"Relabelled hard targets, varied roots: {count-before}", flush=True)

    before = count
    for n in [7, 12, 20, 32, 64]:
        for density in [.08, .2, .5, .8, .97]:
            for _ in range(3):
                root = rng.randrange(6), rng.randrange(n)
                cells = {(i, j) for i in range(6) for j in range(n)
                         if rng.random() < density}
                cells.add((root[0], rng.randrange(n)))
                cells.add((rng.randrange(6), root[1]))
                check(6, n, cells, root)
    print(f"Random six-row targets (up to 64 columns): {count-before}", flush=True)

    before = count
    for m in range(2, 7):
        cells = {(i, i) for i in range(m)}
        for root in itertools.product(range(m), repeat=2):
            check(m, m, cells, root)
    example = json.loads((DEFAULT_DATA.parent / 'strip_example_6x7.json').read_text())
    cells = {tuple(p) for p in example['cells']}
    for root in itertools.product(range(6), range(7)):
        check(6, 7, cells, root)
    print(f"Matching and worked-example root tests: {count-before}", flush=True)

    separation = 0
    for m, n in [(2, 2), (2, 7), (3, 4), (6, 7)]:
        a, b = m-1, n-1
        for r, c in itertools.product(range(m), range(n)):
            A = ([a if i == r else 0 for i in range(m)], [0]*n)
            other = (r+1) % m
            B = ([other]*m, [b if j == c else 0 for j in range(n)])
            for i, j in itertools.product(range(m), range(n)):
                image = step(step({(i, j)}, B), A)
                assert ((a, b) in image) == ((i, j) == (r, c))
                separation += 1
    print(f"Cell-separation checks: {separation}", flush=True)
    print(f"PASS: {count} reaching words replayed; maximum observed length {max_length}")
    print("Reduction counts: " + json.dumps(dict(sorted(kinds.items()))))
    print(f"Elapsed seconds: {time.perf_counter()-start:.6f}")


if __name__ == '__main__':
    main()
