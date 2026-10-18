#!/usr/bin/env python3
"""Independently compare every inherited register-induction literal row."""
import hashlib
import json
import os
from pathlib import Path

ROOT = Path(__file__).resolve().parent
BASE = Path(os.environ.get('ZFC246_BASE', ROOT.parents[1] / 'baseline/context246'))
TABLE = Path(os.environ.get('ZFC246_TABLE', ROOT / 'detector8-context246.tm'))


def parse_table(path):
    table = {}
    for line in path.read_text().splitlines():
        if line and not line.startswith('#'):
            q, b, w, d, t = line.split()
            key = int(q), int(b)
            assert key not in table
            table[key] = [int(w), d, int(t)]
    return table


def rows(term):
    found = []
    if isinstance(term, dict):
        if {'state', 'read', 'row'} <= term.keys():
            found.append(((term['state'], term['read']), term['row']))
        for value in term.values():
            found.extend(rows(value))
    elif isinstance(term, list):
        for value in term:
            found.extend(rows(value))
    return found


original_path = BASE / 'machine/zfc_prefix246_old.tm'
original = parse_table(original_path)
candidate = parse_table(TABLE)
data = json.loads((BASE / 'results/macro-inductions.json').read_text())
assert data['status'] == 'PASS'
assert data['exact_table_sha256'] == hashlib.sha256(original_path.read_bytes()).hexdigest()
expected = {
    'block_theorems': ['seek73_block', 'carry95_block', 'return48_block', 'rollback112_block'],
    'macro_theorems': ['positive_decrement', 'zero_decrement', 'increment'],
    'mark_theorems': [f'mark_{i}' for i in range(9)]}
proofs = []
support = set()
for kind, names in expected.items():
    assert [theorem['name'] for theorem in data[kind]] == names
    for theorem in data[kind]:
        assert theorem['status'] == 'PASS'
        used = rows(theorem)
        assert used
        for key, row in used:
            assert row == original[key] == candidate[key], (theorem['name'], key)
            support.add(key)
        proofs.append(dict(name=theorem['name'], kind=kind,
                           literal_support_rows=[list(key) for key in sorted(set(key for key, _ in used))]))
assert len(support) == 42
assert candidate[6, 1] == original[6, 1] == [1, 'L', 4]
result = dict(status='PASS', baseline_sha256=hashlib.sha256(original_path.read_bytes()).hexdigest(),
    table_sha256=hashlib.sha256(TABLE.read_bytes()).hexdigest(),
    support_rows=42, theorem_count=16, state6_read1=candidate[6, 1], proofs=proofs,
    scope='Literal transition transport for all four block, three register-macro, and nine marking induction traces. Full instruction contracts and blank startup are checked separately.')
(ROOT / 'detector8-support-audit.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({k: v for k, v in result.items() if k != 'proofs'}, indent=2))
