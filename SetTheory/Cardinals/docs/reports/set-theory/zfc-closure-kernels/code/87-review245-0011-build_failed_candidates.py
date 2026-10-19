"""Regenerate three diagnostic 244-state tables from the pinned 245 input.

These are known runtime-contract failures, not smaller correctness results.
Only self-authored code and inert local data are used.
"""
from pathlib import Path
import hashlib
import json
import independent_runtime as r

if not __debug__:
    raise RuntimeError('Assertions are required; do not use optimized Python')


def emit(table, start=95):
    return '#! start ' + str(start) + '\n' + ''.join(
        f'{q} {b} {w} {"R" if d == 1 else "L"} {n}\n'
        for (q, b), (w, d, n) in sorted(table.items()))


def main():
    baseline_path = r.BASE / 'candidate-routing245/zfc_routing245_old.tm'
    assert hashlib.sha256(baseline_path.read_bytes()).hexdigest() == 'f8dbeacdad5fd89c57e3f240781324b09110be8e0ccdb838a9c710fb28d2a267'
    baseline = r.table(baseline_path)
    variants = {
        'candidate_reassociation244_old.tm': (74, {(98, 0): (0, 1, 113), (98, 1): (1, 1, 16)}),
        'candidate_scanner244_old.tm': (58, {(41, 0): (0, -1, 84)}),
        'candidate_appendzero244_old.tm': (255, {(75, 0): (1, -1, 131)}),
    }
    target = r.OUT / 'candidates'
    target.mkdir(parents=True, exist_ok=True)
    identities = {}
    for name, (deleted, changes) in variants.items():
        table = {key: value for key, value in baseline.items() if key[0] != deleted}
        table.update(changes)
        states = {q for q, b in table}
        assert len(states) == 244 and len(table) == 488
        assert {row[2] for row in table.values()} - states == {254}
        text = emit(table)
        (target / name).write_text(text)
        identities[name] = hashlib.sha256(text.encode()).hexdigest()
    grammar = json.loads((r.BASE / 'candidate-routing245/grammar.json').read_text())
    grammar['rules'] = [([w, 'eijkKC', 'eijkfg'] if w == 'eijkKCeijkfg' else [w, a, b])
                        for w, a, b in grammar['rules'] if w != 'KCeijkfg']
    sites = r.sites(grammar)
    (r.OUT / 'obvious244-sites.json').write_text(json.dumps(sites, indent=2) + '\n')
    (r.OUT / 'failed-candidate-identities.json').write_text(json.dumps(identities, indent=2) + '\n')
    print(json.dumps(identities, indent=2))


if __name__ == '__main__':
    main()
