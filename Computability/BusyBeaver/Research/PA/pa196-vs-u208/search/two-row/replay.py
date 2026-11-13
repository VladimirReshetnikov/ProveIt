#!/usr/bin/env python3
"""Replay a two-patched-row contextual-fold screen and its positive control."""
from __future__ import annotations
import argparse
import hashlib
import importlib.util
import json
import subprocess
import tempfile
from pathlib import Path
from zipfile import ZipFile

HERE = Path(__file__).resolve().parent
SEARCH = HERE.parent
REPO = HERE.parents[6]
U209_MEMBER = 'U208_ConPA_2026-10-29/baseline/u209.native.tm'
U209_SHA = 'd0a155d3c683789f3bf5327c0cfb2a0cfd78076af8f1654d4ca426ccbb604d16'

def require(condition, message):
    if not condition:
        raise ValueError(message)

def load_fold():
    spec = importlib.util.spec_from_file_location('pa196_local_folds', SEARCH / 'scan_local_folds.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

def contexts_text(contexts):
    lines = []
    for (q, b), cases in sorted(contexts.items()):
        for tape in cases:
            mask = sum(tape[i] << (i + 2) for i in range(-2, 3))
            require((mask >> 2) & 1 == b, 'context read bit mismatch')
            lines.append(f'{q} {b} {mask}\n')
    return ''.join(lines)

def table_text(table):
    return ''.join(f'{q} {b} {w} {"R" if d == 1 else "L"} {t}\n'
                   for (q, b), (w, d, t) in sorted(table.items()))

def run_engine(binary, directory, table, contexts, count, selected=None):
    table_file, context_file, result_file = (directory / x for x in ('table.txt', 'contexts.txt', 'results.txt'))
    table_file.write_text(table_text(table), encoding='ascii')
    context_data = contexts_text(contexts)
    context_file.write_text(context_data, encoding='ascii')
    args = [str(binary), str(table_file), str(context_file), str(result_file), str(count)]
    if selected is not None: args += [str(q) for q in selected]
    result = subprocess.run(args, check=True, text=True, capture_output=True)
    words = result.stdout.split()
    require(words[::2] == ['initial-patch0', 'viable', 'pairs', 'firstpass', 'survivors'],
            f'unexpected engine output: {result.stdout}')
    counters = dict(zip(words[::2], map(int, words[1::2])))
    records = []
    for line in result_file.read_text().splitlines():
        parts = line.split()
        require(parts[0] in ('rejected', 'SURVIVOR'), f'unexpected record: {line}')
        records.append([parts[0], *map(int, parts[1:])])
    require(sum(r[0] == 'rejected' for r in records) + counters['survivors'] == counters['firstpass'],
            'candidate count mismatch')
    require(sum(r[0] == 'SURVIVOR' for r in records) == counters['survivors'],
            'survivor count mismatch')
    return counters, records, hashlib.sha256(context_data.encode('ascii')).hexdigest()

def independent_failure(table, count, row):
    """Replay a candidate without the C++ prefilter and report its mismatch."""
    _, drop, keep, w0, d0, t0, w1, d1, t1, q, read, mask = row
    old_w, old_d, old_target = table[q, read]
    goal_tape = (mask & ~(1 << 2)) | (old_w << 2)
    project = lambda state: keep if state == drop else state
    goal = (project(old_target), old_d, goal_tape)
    state, pos, tape = keep, 0, mask
    seen = set()
    for k in range(16):
        if state >= count: return 'halt-before-match', k
        if not -2 <= pos <= 2: return 'outside-window', k
        current = (state, pos, tape)
        if current in seen: return 'cycle-before-match', k
        seen.add(current)
        b = (tape >> (pos + 2)) & 1
        w, d, target = ((w0, d0, t0) if b == 0 else (w1, d1, t1)) if state == keep else table[state, b]
        tape = (tape & ~(1 << (pos + 2))) | (w << (pos + 2))
        state, pos = project(target), pos + d
        if (state, pos, tape) == goal: return 'matched', k + 1
    return 'step-limit', 16

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, help='write deterministic JSON receipt')
    args = ap.parse_args()
    fold = load_fold()
    table, digest = fold.read_table(fold.DEFAULT_TABLE)
    contexts, may_halt, closure_size = fold.blank_window_contexts(table, 6)
    require(closure_size == 270067 and sum(map(len, contexts.values())) == 2774 and may_halt,
            'unexpected PA196 blank-window abstraction')
    archive = REPO / 'docs/incoming/U208_ConPA_2026-10-29.zip'
    with ZipFile(archive) as z: data = z.read(U209_MEMBER)
    require(hashlib.sha256(data).hexdigest() == U209_SHA, 'upstream U209 table hash mismatch')
    rows = [line.split() for line in data.decode('ascii').splitlines()
            if line.strip() and not line.startswith('#')]
    labels = sorted({int(row[0]) for row in rows})
    require(len(labels) == 209 and {int(row[4]) for row in rows} - set(labels) == {254},
            'unexpected U209 control states')
    dense = {q: i for i, q in enumerate(labels)}
    dense[254] = 209
    u209 = {(dense[int(q)], int(b)): (int(w), 1 if d == 'R' else -1, dense[int(t)])
            for q, b, w, d, t in rows}
    require(len(u209) == 418 and dense[0] == 0, 'unexpected U209 table domain')
    fold.STATES = 209
    ucontexts, _, _ = fold.blank_window_contexts(u209, 2)
    control_drop, control_keep, helper = (dense[q] for q in (211, 172, 217))
    with tempfile.TemporaryDirectory(prefix='pa196-two-row-') as temp:
        tmp = Path(temp)
        binary = tmp / 'scan'
        subprocess.run(['g++', '-O3', '-std=c++17', '-Wall', '-Wextra', '-Werror',
                        str(HERE / 'scan_two_rows.cpp'), '-o', str(binary)], check=True)
        counters, records, context_sha = run_engine(binary, tmp, table, contexts, 196)
        rejected = [row for row in records if row[0] == 'rejected']
        require(counters == {'initial-patch0': 29964480, 'viable': 51264,
                             'pairs': 40190976, 'firstpass': 4, 'survivors': 0},
                f'unexpected PA196 search outcome: {counters}')
        witnesses = []
        for row in rejected:
            _, drop, keep, w0, d0, t0, w1, d1, t1, q, b, mask = row
            require(any(sum(tape[i] << (i + 2) for i in range(-2, 3)) == mask
                        for tape in contexts[q,b]), 'rejecting window not in abstraction')
            reason, steps = independent_failure(table, 196, row)
            require(reason != 'matched', f'purported failure actually matches: {row}')
            witnesses.append({'drop':drop, 'keep':keep,
                'row0':[w0, 'R' if d0 == 1 else 'L', t0],
                'row1':[w1, 'R' if d1 == 1 else 'L', t1],
                'parent_state':q, 'read':b, 'window_mask':mask,
                'failure':reason, 'steps':steps})
        control_counts, control_records, _ = run_engine(binary, tmp, u209, ucontexts, 209,
                                                         (control_drop, control_keep))
        expected = ['SURVIVOR', control_drop, control_keep, 0, -1, helper,
                    *u209[control_keep, 1]]
        require(expected in control_records, f'known U209 fold missing: {expected}')
    report = {'pa196_table_sha256':digest, 'window_invariant_radius':6,
              'closure_windows':closure_size, 'projected_contexts':2774,
              'context_encoding_sha256':context_sha, 'abstract_halt_reachable':may_halt,
              'max_child_steps':16, 'active_window_radius':2,
              'screen_counts':counters, 'representative_pass_rejections':witnesses,
              'u209_member_sha256':U209_SHA, 'u209_control_counts':control_counts,
              'u209_control_native_drop_keep_helper':[211,172,217],
              'u209_control_dense_drop_keep_helper':[control_drop,control_keep,helper],
              'u209_control_known_fold_recovered':True}
    out = json.dumps(report, indent=2, sort_keys=True) + '\n'
    print(out, end='')
    if args.output: args.output.write_text(out)

if __name__ == '__main__': main()
