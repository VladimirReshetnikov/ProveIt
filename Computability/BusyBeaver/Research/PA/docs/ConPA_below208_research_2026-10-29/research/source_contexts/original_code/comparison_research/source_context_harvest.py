#!/usr/bin/env python3
"""Harvest bounded tape windows while replaying all canonical U208 contracts.

This is discovery data, not a new formal invariant certificate. Variable runs
are independently widened to all lengths above their affine constant. List
atoms are widened to arbitrary finite lists of their indicated block family.
Compressed scan states receive every window; startup is simulated literally.
Any candidate found using these contexts still requires a fresh complete
symbolic runtime replay and literal blank-startup check.
"""
import argparse
from functools import lru_cache
import hashlib
import importlib.util
import itertools
import json
from pathlib import Path
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
PACKET = ROOT / 'sources208/U208_ConPA_Entry_Context_2026-10-29/u208_conpa_entry_context_2026-10-29'


@lru_cache(None)
def any_bits(n):
    return frozenset(''.join(x) for x in itertools.product('01', repeat=n))


def bounded_atoms(atoms, n):
    result = []
    lower = 0
    for atom in atoms:
        if atom[0] == 'run':
            affine = atom[2]
            count = min(n, affine[0])
            variable = any(affine[1:])
            if not variable and not count:
                continue
            result.append(('run', atom[1], count, variable))
            lower += count
        elif atom[0] == 'list':
            result.append(('list', atom[1], atom[3]))
        else:
            result.append((atom[0],))
            break
        if lower >= n:
            break
    return tuple(result)


@lru_cache(None)
def prefix_words(atoms, n):
    if n == 0:
        return frozenset([''])
    if not atoms or atoms[0][0] == 'opaque':
        return any_bits(n)
    atom, rest = atoms[0], atoms[1:]
    if atom[0] == 'blank':
        return frozenset(['0' * n])
    if atom[0] == 'run':
        _, b, lower, variable = atom
        lower = min(lower, n)
        counts = range(lower, n + 1) if variable else [lower]
        return frozenset(str(b) * count + suffix
                         for count in counts
                         for suffix in prefix_words(rest, n - count))
    if atom[0] != 'list':
        raise ValueError(atom)
    family, reverse = atom[1:3]
    if len(atom) == 4:
        value = atom[3]
        word = ('0' + '1' * (value + 1)) if family == 'B' else ('10' + '1' * value)
        if reverse:
            word = word[::-1]
        block = tuple(('run', int(bit), 1, False) for bit in word)
    elif (family, reverse) == ('B', False):
        block = (('run', 0, 1, False), ('run', 1, 1, True))
    elif (family, reverse) == ('B', True):
        block = (('run', 1, 1, True), ('run', 0, 1, False))
    elif (family, reverse) == ('C', False):
        block = (('run', 1, 1, False), ('run', 0, 1, False), ('run', 1, 0, True))
    elif (family, reverse) == ('C', True):
        block = (('run', 1, 0, True), ('run', 0, 1, False), ('run', 1, 1, False))
    else:
        raise ValueError(atom)
    return prefix_words(rest, n) | prefix_words(block + atoms, n)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--radius', type=int, default=4)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    radius = args.radius
    sys.path.insert(0, str(PACKET / 'code'))
    import check_runtime as replay
    symbolic = replay.s
    table_path = PACKET / 'machine/u208.native.tm'
    table = replay.read(table_path)
    windows = {q: set() for q, b in table}
    calls = 0
    compressed_states = set()
    complete = set(range(1 << (radius * 2 + 1)))
    original = symbolic.State.step
    started = time.monotonic()

    @lru_cache(None)
    def nearby(left, right, direction):
        nl = radius if direction == 1 else radius + 1
        nr = radius + 1 if direction == 1 else radius
        return frozenset(int(a[::-1] + b, 2)
                         for a in prefix_words(left, nl)
                         for b in prefix_words(right, nr))

    def step(state, table, lemmas, clock, motion):
        nonlocal calls
        state.key()
        if state.q in windows and windows[state.q] != complete:
            nl = radius if state.direction == 1 else radius + 1
            nr = radius + 1 if state.direction == 1 else radius
            local = nearby(bounded_atoms(state.left, nl),
                           bounded_atoms(state.right, nr), state.direction)
            windows[state.q].update(local)
        q = state.q
        answer = original(state, table, lemmas, clock, motion)
        if answer[2][0] in ('unary', 'list'):
            # The skipped interior is deliberately overapproximated completely.
            # This is conservative for the scanner entry and internal loop state.
            windows[q] = set(complete)
            compressed_states.add(q)
        calls += 1
        return answer

    symbolic.State.step = step
    output_dir = args.output.parent / ('runtime_radius' + str(radius))
    result = replay.check(PACKET / 'machine', output_dir)
    q = head = 0
    ones = set()
    for tick in range(48140):
        bits = ''.join(str(int(head + d in ones)) for d in range(-radius, radius + 1))
        windows[q].add(int(bits, 2))
        w, d, z = table[q, int(head in ones)]
        ones.add(head) if w else ones.discard(head)
        q, head = z, head + d
    result = {'scope': __doc__, 'radius': radius,
              'input_table': str(table_path.relative_to(ROOT)),
              'input_sha256': hashlib.sha256(table_path.read_bytes()).hexdigest(),
              'runtime': result, 'hook_calls': calls,
              'startup_steps': 48140, 'startup_endpoint': [q, head],
              'compressed_states_widened_to_every_window': sorted(compressed_states),
              'window_count': sum(map(len, windows.values())),
              'window_counts': {q: len(v) for q, v in windows.items()},
              'windows': {q: sorted(v) for q, v in windows.items()},
              'seconds': time.monotonic() - started,
              'cache_info': {'nearby': str(nearby.cache_info()),
                             'prefix_words': str(prefix_words.cache_info())}}
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k not in ('windows', 'runtime', 'window_counts')}, indent=2))


if __name__ == '__main__':
    main()
