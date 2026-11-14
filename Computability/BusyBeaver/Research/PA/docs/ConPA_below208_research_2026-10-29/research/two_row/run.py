#!/usr/bin/env python3
"""Reproduce the bounded two-row quotient screen; not a nonhalting proof.

All contexts are generated from literal tables. Each disjunctive cylinder is
sampled by three deterministic exterior completions in search.cpp. A survivor
would require an additional exact whole-tape proof; the retained runs have none.
"""
import argparse
import gzip
import hashlib
import itertools
import json
import os
from pathlib import Path
import re
import subprocess
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read_table(path):
    table = {}
    for line in path.read_text().splitlines():
        if not line or line.startswith('#'):
            continue
        q, b, w, d, z = line.split()
        q, b, w, z = map(int, (q, b, w, z))
        require((q, b) not in table and b in (0, 1) and w in (0, 1)
                and d in ('L', 'R'), 'Malformed literal table')
        table[q, b] = w, (1 if d == 'R' else -1), z
    states = {q for q, b in table}
    require(set(table) == {(q, b) for q in states for b in (0, 1)},
            'Incomplete table')
    require({z for w, d, z in table.values()} <= states | {254}, 'Unknown target')
    return table


def remove_subsumed(items):
    result, sets = [], []
    for item in sorted(set(items), key=lambda c: (len(c), c)):
        values = frozenset(item)
        if not any(previous <= values for previous in sets):
            result.append(item)
            sets.append(values)
    return result


def contexts(table, depth):
    states = {q for q, b in table}
    current = {q: [()] for q in states}
    for _ in range(depth):
        following = {q: [] for q in states}
        following[0] = [()]
        for (q, b), (w, direction, target) in table.items():
            if target not in states:
                continue
            for context in current[q]:
                cells = dict(context)
                if 0 in cells and cells[0] != b:
                    continue
                cells[0] = w
                following[target].append(tuple(sorted(
                    (position-direction, value) for position, value in cells.items())))
        current = {q: remove_subsumed(cases) for q, cases in following.items()}
    return current


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--class', dest='family', choices=['A', 'B', 'control'], default='A')
    parser.add_argument('--depth', type=int, default=12)
    parser.add_argument('--bound', type=int, default=71)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--contexts', type=Path,
                        help='Use an explicit JSON state->list of cell dictionaries instead of histories')
    parser.add_argument('--cxx', default='g++')
    args = parser.parse_args()
    require(0 <= args.depth <= 20 and 1 <= args.bound <= 120, 'Bounds outside supported range')
    begin = time.monotonic()
    snapshot = {'A': 'u208_entry_primary', 'B': 'u208_entry_alternative',
                'control': 'u209_joint'}[args.family]
    table_path = ROOT / 'baseline/snapshots' / snapshot / 'native.tm'
    table = read_table(table_path)
    if args.contexts:
        if args.contexts.suffix == '.gz':
            with gzip.open(args.contexts, 'rt') as stream:
                loaded = json.load(stream)
        else:
            loaded = json.loads(args.contexts.read_text())
        ctx = {int(q): [tuple(sorted((int(p), int(v)) for p, v in c.items()))
                        for c in cases] for q, cases in loaded.items()}
        require(set(ctx) == {q for q, b in table}, 'Explicit context state coverage')
    else:
        ctx = contexts(table, args.depth)
    args.output.mkdir(parents=True, exist_ok=True)
    context_path = args.output / 'contexts.txt'
    with context_path.open('w') as output:
        for q, cylinders in sorted(ctx.items()):
            for cells in cylinders:
                require(all(-128 <= p <= 128 and v in (0, 1) for p, v in cells),
                        'Invalid context cell')
                output.write(str(q)+' '+str(len(cells))+' '+
                             ' '.join(f'{p} {v}' for p, v in cells)+'\n')
    pairs_path = args.output / 'pairs.txt'
    pairs = [(211, 172)] if args.family == 'control' else [
        (max(q, r), min(q, r)) for q, r in itertools.combinations(sorted(ctx), 2)]
    pairs_path.write_text(''.join(f'{q} {r}\n' for q, r in pairs))
    executable = args.output / 'search'
    command = [args.cxx, '-O3', '-std=c++17', str(HERE/'search.cpp'), '-o', str(executable)]
    subprocess.run(command, check=True)
    run_command = [str(executable.resolve()), str(table_path), str(context_path.resolve()),
                   str(args.bound), str(pairs_path.resolve())]
    result = subprocess.run(run_command, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, check=True)
    (args.output/'search.log').write_text(result.stdout)
    lines = result.stdout.splitlines()
    finish = next((line for line in reversed(lines) if line.startswith('DONE ')), None)
    require(finish is not None, 'Incomplete search')
    fields = finish.split()[1:]
    census = {fields[i]: int(fields[i+1]) for i in range(0, len(fields), 2)}
    hits = [line for line in lines if line.startswith('HIT ')]
    require(census['pairs'] == len(pairs) and census['hits'] == len(hits), 'Search census mismatch')
    if args.family == 'control':
        require(hits == ['HIT 211 172 0 -1 217 1 1 184'], 'Known fold was not recovered exactly')
    report = {'status': 'BOUNDED_REJECTION_SCREEN_COMPLETE', 'family': args.family,
              'table_sha256': hashlib.sha256(table_path.read_bytes()).hexdigest(),
              'source_sha256': hashlib.sha256((HERE/'search.cpp').read_bytes()).hexdigest(),
              'context_kind': 'supplied disjunctive cylinders' if args.contexts else 'all-tape histories',
              'history_depth': None if args.contexts else args.depth,
              'context_cylinders': sum(map(len, ctx.values())), 'new_step_bound': args.bound,
              'completions_per_cylinder_and_read_bit': 3, 'random_seed': 20261030,
              'start_pairs_included': args.family != 'control', 'census': census,
              'hits': hits, 'seconds': time.monotonic()-begin,
              'scope': 'One old step against positive child block; identity tape/head boundary; '
                       'state identification; both keeper rows arbitrary with retained working targets. '
                       'Finite completions and overapproximated contexts are rejection tests, not '
                       'a lower bound on consistency machines.'}
    (args.output/'receipt.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
