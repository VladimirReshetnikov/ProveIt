#!/usr/bin/env python3
"""Independent literal audit of PA195's inherited register oracle.

Reads the submitted table and Lean reference text directly; does not import
the candidate builder or symbolic runtime. This is an executable audit, not
a newly elaborated Lean theorem.
"""
import ast
import hashlib
import json
from pathlib import Path
import re

BASE = Path(__file__).resolve().parents[1]
NEW = BASE / 'pa195'
UP = BASE / 'reference_sources'
OLD = NEW / 'vendor/reference'


def read_table(path):
    rows = {}
    for line in path.read_text().splitlines():
        if not line or line.startswith('#'):
            continue
        q, b, w, d, n = line.split()
        q, b, w, n = map(int, (q, b, w, n))
        if (q, b) in rows or b not in (0, 1) or w not in (0, 1) or d not in ('L', 'R'):
            raise ValueError('malformed table row')
        rows[q, b] = w, d == 'R', n
    return rows


def main():
    native = read_table(NEW / 'pa195.native.tm')
    dense = read_table(NEW / 'pa195.tm')
    labels = json.loads((NEW / 'labels.json').read_text())
    assert len(labels) == len(set(labels)) == 196
    assert labels[0] == 74 and labels[-1] == 254
    assert set(dense) == {(q, b) for q in range(195) for b in (0, 1)}
    assert {(labels[q], b): (w, d, labels[n])
            for (q, b), (w, d, n) in dense.items()} == native
    native_lean = (UP / 'M6/Native.lean').read_text()
    stated = ast.literal_eval(re.search(r'def boxStates : List Nat :=\s*(\[[^\]]+\])', native_lean)[1])
    oracle_source = (NEW / 'vendor/symbolic_runtime.py').read_text()
    python_set = ast.literal_eval(re.search(r'BOXSTATES=(\{[^\}]+\})', oracle_source)[1])
    assert python_set == set(stated)
    source = (UP / 'M6/Reference230.lean').read_text().split('def table230')[1]
    raw_rows = re.findall(r'\(some \((true|false), (true|false), (\d+)\), some \((true|false), (true|false), (\d+)\)\)', source)
    assert len(raw_rows) == 230
    ref = {}
    for q, row in enumerate(raw_rows):
        for b in (0, 1):
            w, d, n = row[3*b:3*b+3]
            ref[q, b] = int(w == 'true'), d == 'true', int(n)
    required = [(q, b) for q in stated for b in (0, 1) if (q, b) not in [(113, 0), (198, 0)]]
    assert len(required) == 44
    assert all(native[key] == ref[key] for key in required)
    assert native[198, 0] == (1, False, 40)
    old_labels = ast.literal_eval(re.search(r'def labels : List Nat := (\[[^\n]+\])',
                                         (OLD / 'PA196/Conjugacy.lean').read_text())[1])
    old_dense = read_table(OLD / 'data/pa196.tm')
    old = {(old_labels[q], b): (w, d, old_labels[n]) for (q, b), (w, d, n) in old_dense.items()}
    assert all(native[q, b] == old[q, b] for q in stated for b in (0, 1))
    result = {
        'candidate_dense_sha256': hashlib.sha256((NEW / 'pa195.tm').read_bytes()).hexdigest(),
        'literal_binary_rows': len(dense),
        'working_states': 195,
        'dense_native_conjugacy': True,
        'box_state_set_exact': True,
        'box_states': stated,
        'reference230_rows_exact': len(required),
        'native_append_one_tail_198_0': [1, 'L', 40],
        'total_rows_required_by_native_box_theorem': 45,
        'total_rows_preserved_by_candidate_checker': 46,
        'extra_preserved_row': [113, 0],
        'all_46_rows_identical_to_published_pa196': True,
        'new_kernel_checked_theorem': False,
        'scope': 'Literal inheritance premises for M6.Native.boxLemmas; symbolic executor audit is a separate written proof.'
    }
    (Path(__file__).parent / 'engine_audit.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
