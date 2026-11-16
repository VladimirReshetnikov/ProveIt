#!/usr/bin/env python3
"""Replay the exhaustive two-arbitrary-row screen and its small-table controls."""
from __future__ import annotations
import argparse
import hashlib
import importlib.util
from itertools import combinations, product
import json
from pathlib import Path
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
HELPER = HERE.parent / 'helper-row'
EXPECTED = {'pairs': 38220, 'plain': 0, 'first_keys': 103550,
            'first_patches': 81183200, 'one': 0, 'second_keys': 528136,
            'second_patches': 414058624, 'passes': 0}
SYNTHETIC = {
    (0, 0): (1, -1, 0), (0, 1): (0, -1, 3),
    (1, 0): (0, -1, 3), (1, 1): (1, -1, 2),
    (2, 0): (1, -1, 1), (2, 1): (1, -1, 2),
    (3, 0): (0, 1, 2), (3, 1): (1, 1, 2),
}


def need(ok, message):
    if not ok:
        raise ValueError(message)


def load(path):
    spec = importlib.util.spec_from_file_location('helper_support', path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def run_engine(binary, temp, table, contexts, n, selected=None):
    table_file, context_file, output_file = (temp / x for x in ('table', 'contexts', 'output'))
    table_file.write_text(support.table_text(table), encoding='ascii')
    context_data = support.contexts_text(contexts)
    context_file.write_text(context_data, encoding='ascii')
    argv = [str(binary), str(table_file), str(context_file), str(output_file), str(n)]
    if selected is not None:
        argv += [str(q) for q in selected]
    result = subprocess.run(argv, capture_output=True, text=True, check=True)
    words = result.stdout.split()
    need(words[::2] == ['pairs', 'plain', 'first_keys', 'first_patches', 'one',
                        'second_keys', 'second_patches', 'passes'], 'bad engine counters')
    counts = dict(zip(words[::2], map(int, words[1::2])))
    lines = [x.split() for x in output_file.read_text().splitlines()]
    need(all(x[0] in ('ONE', 'PASS') for x in lines), 'bad engine output')
    need(sum(x[0] == 'ONE' for x in lines) == counts['one'] and
         sum(x[0] == 'PASS' for x in lines) == counts['passes'], 'output count mismatch')
    return counts, lines, hashlib.sha256(context_data.encode('ascii')).hexdigest()


def block(table, n, drop, keep, patches, q, bit, mask):
    """Independent straight-line checker: no visited-row pruning."""
    project = lambda x: keep if x == drop else x
    w, d, dest = table[q, bit]
    goal = project(dest), d, (mask & ~4) | (w << 2)
    state, head, tape = project(q), 0, mask
    for _ in range(16):
        if state >= n or not -2 <= head <= 2:
            return False
        read = (tape >> (head + 2)) & 1
        w, d, dest = patches.get((state, read), table[state, read])
        tape = (tape & ~(1 << (head + 2))) | (w << (head + 2))
        state, head = project(dest), head + d
        if (state, head, tape) == goal:
            return True
    return False


def brute_synthetic():
    drop, keep, n = 2, 0, 4
    keys = [(q, bit) for q in range(n) if q != drop for bit in (0, 1)]
    rows = list(product((0, 1), (-1, 1), (0, 1, 3, 4)))
    def passes(patches):
        return all(block(SYNTHETIC, n, drop, keep, patches, q, (mask >> 2) & 1, mask)
                   for q in range(n) for mask in range(32))
    plain = passes({})
    one = [(key, row) for key in keys for row in rows if passes({key: row})]
    two = [(a, ra, b, rb) for a, b in combinations(keys, 2)
           for ra in rows for rb in rows if passes({a: ra, b: rb})]
    return plain, one, two


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path)
    args = ap.parse_args()
    fold = support.load_fold()
    table, digest = fold.read_table(fold.DEFAULT_TABLE)
    contexts, may_halt, closure = fold.blank_window_contexts(table, 6)
    need((closure, sum(map(len, contexts.values())), may_halt) == (270067, 2774, True),
         'PA196 invariant changed')
    synthetic_contexts = {(q, b): [] for q in range(4) for b in (0, 1)}
    for q in range(4):
        for mask in range(32):
            synthetic_contexts[q, (mask >> 2) & 1].append(
                {i: (mask >> (i + 2)) & 1 for i in range(-2, 3)})
    plain, one, two = brute_synthetic()
    expected_two = [((0, 0), (1, -1, 1), (1, 1), (1, -1, 3))]
    need(not plain and not one and two == expected_two,
         f'synthetic exhaustive brute force changed: {plain}, {one}, {two}')
    with tempfile.TemporaryDirectory(prefix='pa196-two-helper-') as tmp:
        temp = Path(tmp); binary = temp / 'scan'
        subprocess.run(['g++', '-O3', '-std=c++17', '-Wall', '-Wextra', '-Werror',
                        str(HERE / 'scan.cpp'), '-o', str(binary)], check=True)
        controls, lines, _ = run_engine(binary, temp, SYNTHETIC, synthetic_contexts, 4, (2, 0))
        need(controls == {'pairs': 1, 'plain': 0, 'first_keys': 1,
                          'first_patches': 16, 'one': 0, 'second_keys': 2,
                          'second_patches': 32, 'passes': 1}, 'synthetic engine counts changed')
        need(lines == [['PASS', '2', '0', '0', '1', '-1', '1', '3', '1', '-1', '3']],
             'synthetic engine survivor changed')
        counts, lines, context_hash = run_engine(binary, temp, table, contexts, 196)
        need(counts == EXPECTED and not lines, f'PA196 screen changed: {counts}, {lines}')
    result = {
        'table_sha256': digest, 'radius': 6, 'closure_windows': closure,
        'projected_contexts': 2774, 'context_encoding_sha256': context_hash,
        'abstract_halt_reachable': may_halt, 'active_window_radius': 2,
        'max_child_steps': 16, 'counts': counts,
        'synthetic_original_table': support.table_text(SYNTHETIC),
        'synthetic_drop_keep': [2, 0], 'synthetic_counts': controls,
        'synthetic_brute_force_no_patch_survivors': int(plain),
        'synthetic_brute_force_one_patch_survivors': len(one),
        'synthetic_brute_force_two_patch_survivors': len(two),
        'synthetic_survivor': [list(two[0][0]), list(two[0][1]),
                               list(two[0][2]), list(two[0][3])],
        'scope': 'Direct state projection, one removed state, at most two changed rows; '
                 'positive blocks <= 16 restricted to five cells.'}
    data = json.dumps(result, indent=2, sort_keys=True) + '\n'
    print(data, end='')
    if args.output:
        args.output.write_text(data)


support = load(HELPER / 'replay.py')
if __name__ == '__main__':
    main()
