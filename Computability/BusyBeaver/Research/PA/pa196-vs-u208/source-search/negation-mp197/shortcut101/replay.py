#!/usr/bin/env python3
"""Check a blank-start stuttering shortcut in the combined 197-state machine."""
from collections import deque
import argparse
import hashlib
import importlib.util
import itertools
import json
from pathlib import Path
import subprocess
import sys
import tempfile
from zipfile import ZipFile

HERE = Path(__file__).resolve().parent
SOURCE = HERE.parent
REPO = HERE.parents[7]
ARCHIVE = REPO / 'docs/incoming/pa_consistency_research_2026-11-13.zip'
PINS = {
    ARCHIVE: '466c804d54495d3347252a98788af021aecc459b041fcc1733b3adf1ff1e943b',
    SOURCE / 'machine.native.tm': 'a2db6b2791912d90cb87b6b310157180917c5652d85ecb09a506e0de1628a264',
    SOURCE / 'source.tree.json': '7d01a47445daf5ff804d32af8886364b3ee9e9f38efaa1e9d147d7989c28479e',
}


def need(ok, msg):
    if not ok:
        raise ValueError(msg)


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    obj = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(obj)
    return obj


def closure(table):
    """Radius-six blank-window closure; audit every successor after discovery."""
    radius, width = 6, 13
    mask, mid = (1 << width) - 1, 1 << radius
    visited = {(0, 0)}
    queue = deque(visited)
    may_halt = False
    while queue:
        q, bits = queue.popleft()
        read = (bits >> radius) & 1
        write, direction, target = table[q, read]
        bits = (bits | mid) if write else (bits & ~mid)
        if target == 197:
            may_halt = True
            continue
        for fresh in (0, 1):
            new_bits = ((bits >> 1) | (fresh << (width-1)) if direction == 1
                        else ((bits << 1) & mask) | fresh)
            state = target, new_bits
            if state not in visited:
                visited.add(state)
                queue.append(state)
    need((0, 0) in visited, 'blank seed missing')
    halt_edges = 0
    for q, old_bits in visited:
        read = (old_bits >> radius) & 1
        write, direction, target = table[q, read]
        bits = (old_bits | mid) if write else (old_bits & ~mid)
        if target == 197:
            halt_edges += 1
            continue
        for fresh in (0, 1):
            new_bits = ((bits >> 1) | (fresh << (width-1)) if direction == 1
                        else ((bits << 1) & mask) | fresh)
            need((target, new_bits) in visited, 'closure has a missing successor')
    projected = {(q, (bits >> (radius-2)) & 31) for q, bits in visited}
    return visited, projected, may_halt, halt_edges


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--out-dir', type=Path)
    args = parser.parse_args()
    need(__debug__, 'the inherited symbolic checker requires Python assertions')
    for path, digest in PINS.items():
        need(hashlib.sha256(path.read_bytes()).hexdigest() == digest, f'input changed: {path}')
    rows = {}
    for line in (SOURCE / 'machine.native.tm').read_text().splitlines():
        q, b, w, direction, n = line.split()
        key = int(q), int(b)
        need(key not in rows and direction in ('L', 'R'), 'bad native row')
        rows[key] = int(w), direction, int(n)
    labels = [74] + sorted({q for q, _ in rows} - {74})
    need(len(labels) == 197 and set(rows) == set(itertools.product(labels, (0, 1))),
         'working-state row census changed')
    encode = {q: i for i, q in enumerate(labels)}
    encode[254] = 197
    need(all(n in encode for _, _, n in rows.values()), 'unknown destination')
    dense = {(encode[q], b): (w, 1 if d == 'R' else -1, encode[n])
             for (q, b), (w, d, n) in rows.items()}
    visited, projected, may_halt, halt_edges = closure(dense)
    masks = sorted(bits for q, bits in projected if q == encode[101] and not (bits & 4))
    need(len(visited) == 266771 and may_halt and len(masks) == 4 and
         all(not (bits & 2) for bits in masks), 'expected blank-window invariant failed')
    independent = load('shortcut101_independent_closure',
                       SOURCE.parents[1] / 'search/scan_local_folds.py')
    independent.STATES = 197
    contexts, halt2, count2 = independent.blank_window_contexts(dense, 6)
    projected2 = {(q, sum(tape[x] << (x+2) for x in range(-2, 3)))
                  for (q, _), cases in contexts.items() for tape in cases}
    need(count2 == len(visited) and halt2 == may_halt and projected2 == projected,
         'independent radius-six projection differs')
    need(rows[101, 0] == (0, 'L', 26) and rows[26, 0] == (0, 'R', 194) and
         rows[194, 0] == (0, 'R', 17), 'original detour differs')
    # Compare every local configuration admitted by the projected invariant.
    for bits in masks:
        tape = {x: (bits >> (x+2)) & 1 for x in range(-2, 3)}
        candidate_tape = dict(tape)
        q, head = 101, 0
        for _ in range(3):
            write, direction, q = rows[q, tape[head]]
            tape[head] = write
            head += 1 if direction == 'R' else -1
        candidate_tape[0] = 0
        need((q, head, tape) == (17, 1, candidate_tape), f'macro mismatch: {bits}')
    candidate = dict(rows)
    candidate[101, 0] = (0, 'R', 17)
    table_text = ''.join(f'{q} {b} {w} {d} {n}\n'
                         for (q, b), (w, d, n) in sorted(candidate.items()))
    need((HERE / 'machine.native.tm').read_text() == table_text,
         'retained candidate differs from reconstructed table')
    with tempfile.TemporaryDirectory(prefix='pa197-shortcut101-') as directory:
        root = Path(directory)
        files = ['verification/check.py', 'verification/symbolic.py',
                 'reference/pa196/PA196/Conjugacy.lean', 'reference/pa196/PA196/Program.lean',
                 'reference/pa196/data/pa196.tm']
        with ZipFile(ARCHIVE) as z:
            for rel in files:
                path = root / rel
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(z.read('pa_consistency_research/' + rel))
        sys.path.insert(0, str(root / 'verification'))
        check = load('shortcut101_archive_checker', root / files[0])
        tree = check.tuplify(json.loads((SOURCE / 'source.tree.json').read_text()))
        original_startup = check.startup(rows)
        result = check.run('shortcut101', candidate, tree)
        need(original_startup == 58154 and result == {
            'name': 'shortcut101', 'working_states': 197, 'rows': 394,
            'engine_agreement_rows': 42, 'startup_steps': 58142,
            'symbolic': {'sites': 3573, 'cases': 4641, 'max_symbolic_steps': 515},
            'passed': True}, 'symbolic contracts or startup differ')

    seen, todo = {74}, [74]
    for q in todo:
        for b in (0, 1):
            n = candidate[q, b][2]
            if n != 254 and n not in seen:
                seen.add(n)
                todo.append(n)
    need(len(seen) == 197, 'candidate state reachability census changed')

    out = {'source_table_sha256': PINS[SOURCE / 'machine.native.tm'],
           'source_tree_sha256': PINS[SOURCE / 'source.tree.json'],
           'archive_sha256': PINS[ARCHIVE],
           'candidate_table_sha256': hashlib.sha256(table_text.encode()).hexdigest(),
           'radius': 6, 'blank_start_closure': len(visited),
           'projected_contexts': len(projected), 'abstract_halt_reachable': may_halt,
           'abstract_halt_edges': halt_edges,
           'native101_read0_five_cell_masks': masks,
           'left_neighbor_always_zero': True,
           'old_three_steps_match_new_one_on_all_projected_contexts': True,
           'all_closure_edges_audited': True, 'independent_projection_matches': True,
           'original_startup_steps': original_startup,
           'candidate_symbolic_and_startup': result,
           'reachable_working_states': len(seen),
           'scope': 'Conditional blank-start stuttering argument and executable symbolic contracts; no PA theorem.'}
    text = json.dumps(out, indent=2, sort_keys=True) + '\n'
    print(text, end='')
    if args.output:
        args.output.write_text(text)
    if args.out_dir:
        args.out_dir.mkdir(parents=True, exist_ok=True)
        (args.out_dir / 'machine-with-start.native.tm').write_text('#! start 74\n' + table_text)


if __name__ == '__main__':
    main()
