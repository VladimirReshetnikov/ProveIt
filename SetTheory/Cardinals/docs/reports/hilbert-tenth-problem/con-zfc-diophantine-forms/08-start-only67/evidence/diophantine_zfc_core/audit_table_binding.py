#!/usr/bin/env python3
"""Independent inert-data binding audit. Does not import upstream modules."""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parent
SRC = ROOT / 'sources'
DENSE_TM = SRC / 'k215.tm'

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def parse_tm(path):
    actions = {}
    start = None
    for line in path.read_text().splitlines():
        if line.startswith('#! start '):
            start = int(line.split()[-1])
        elif line.startswith('#') or not line.strip():
            continue
        else:
            q, read, write, move, target = line.split()
            q, read, write, target = map(int, (q, read, write, target))
            assert read in (0, 1) and write in (0, 1)
            assert move in ('L', 'R')
            assert (q, read) not in actions
            actions[q, read] = (write, move, target)
    return start, actions

def lean_bool(b):
    assert b in ('false', 'true')
    return int(b == 'true')

def parse_lean_dense(path):
    source = path.read_text()
    block = source.split('def rows215 :', 1)[1].split(' := [', 1)[1].split(']\n', 1)[0]
    rows = re.findall(r'\(\((true|false), (true|false), (\d+)\), '
                      r'\((true|false), (true|false), (\d+)\)\)', block)
    assert len(rows) == 215
    actions = {}
    for q, row in enumerate(rows):
        for read in (0, 1):
            write, move, target = row[3*read:3*read+3]
            actions[q, read] = (lean_bool(write), 'R' if move == 'true' else 'L', int(target))
    labels_text = source.split('def denseLabels : List Nat := [', 1)[1].split(']', 1)[0]
    labels = list(map(int, labels_text.split(', ')))
    assert len(labels) == 215 and len(set(labels)) == 215
    return actions, labels

def parse_lean_sparse(path):
    source = path.read_text()
    block = source.split('def table215 :', 1)[1].split(' := [', 1)[1].split(']\n', 1)[0]
    row_expr = r'\((none|some \((?:true|false), (?:true|false), \d+\)), '
    row_expr += r'(none|some \((?:true|false), (?:true|false), \d+\))\)'
    rows = re.findall(row_expr, block)
    assert len(rows) == 226
    actions = {}
    for q, row in enumerate(rows):
        for read, action in enumerate(row):
            if action == 'none':
                continue
            write, move, target = re.fullmatch(r'some \((true|false), (true|false), (\d+)\)', action).groups()
            actions[q, read] = (lean_bool(write), 'R' if move == 'true' else 'L', int(target))
    return actions

def main():
    start, dense = parse_tm(DENSE_TM)
    native_start, native = parse_tm(SRC / 'k215.native.tm')
    lean_dense, labels = parse_lean_dense(SRC / 'KDense215.lean')
    lean_sparse = parse_lean_sparse(SRC / 'KTable215.lean')
    assert start == native_start == 0
    assert len(dense) == len(native) == len(lean_dense) == len(lean_sparse) == 430
    assert set(dense) == {(q, b) for q in range(215) for b in (0, 1)}
    assert dense == lean_dense
    aliases = {301: 102, 302: 120, 254: 230}
    rename = lambda q: aliases.get(q, q)
    renamed_native = {(rename(q), b): (w, d, rename(t))
                      for (q, b), (w, d, t) in native.items()}
    assert renamed_native == lean_sparse
    expand = lambda q: labels[q] if q < len(labels) else 230
    records = []
    for (q, b), (w, d, t) in sorted(dense.items()):
        assert t <= 215
        expected_sparse = (w, d, expand(t))
        assert lean_sparse[expand(q), b] == expected_sparse
        records.append(dict(dense_state=q, read=b, dense_action=[w, d, t],
                            sparse_state=expand(q), sparse_action=list(expected_sparse),
                            literal_dense_equal=True, renamed_sparse_equal=True))
    assert labels[0] == 0 and labels[-2:] == [102, 120]
    assert not any(q == 230 for q, _ in lean_sparse)
    terminal_actions = [r for r in records if r['dense_action'][-1] == 215]
    assert len(terminal_actions) == 1
    report = dict(
        status='PASS', commit='cdd582bec13f908df3711fa9e05d1ddac368a5db',
        method='Independent regex parsing of inert pinned sources; no upstream code executed.',
        dense_tm_sha256=sha(DENSE_TM), native_tm_sha256=sha(SRC / 'k215.native.tm'),
        formal_dense_sha256=sha(SRC / 'KDense215.lean'),
        formal_sparse_sha256=sha(SRC / 'KTable215.lean'),
        initial_state=0, blank_symbol=0, two_way_tape=True,
        working_states=215, total_actions=430, dense_halt=215, sparse_halt=230,
        native_aliases={str(k): v for k, v in aliases.items()},
        dense_labels=labels, terminal_actions=terminal_actions,
        endpoint='KEndpoint215.blank_halts_iff_zfc_refutation',
        verification_boundary='Row identity and renaming audited independently; Lean not recompiled.',
        actions=records)
    out = ROOT / 'table_binding.json'
    out.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k not in ('actions', 'dense_labels')}, indent=2))

if __name__ == '__main__':
    main()
