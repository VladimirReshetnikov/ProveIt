#!/usr/bin/env python3
"""Verify saved low-level search artifacts; no claim of search rerun."""
from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent

def require(condition, message):
    if not condition:
        raise ValueError(message)

def read_table(path):
    table = {}
    for line in path.read_text().splitlines():
        line = line.split('#', 1)[0].strip()
        if not line:
            continue
        q, b, w, d, target = line.split()
        q, b, w, target = map(int, (q, b, w, target))
        require((q, b) not in table and 0 <= q < 196 and b in (0, 1)
                and w in (0, 1) and d in ('L', 'R')
                and 0 <= target <= 196, 'invalid transition')
        table[q, b] = w, 1 if d == 'R' else -1, target
    require(set(table) == {(q, b) for q in range(196) for b in (0, 1)},
            'incomplete transition domain')
    return table

def main():
    record = json.loads((HERE / 'receipt.json').read_text())
    for run in record['runs']:
        for key, hash_key in [('machine', 'machine_sha256'), ('contexts', 'context_sha256')]:
            require(hashlib.sha256((HERE / run[key]).read_bytes()).hexdigest()
                    == run[hash_key], 'hash mismatch: ' + run[key])
        require(run['pairs'] == 38220 and run['survivors'] == run['plain'] == 0,
                'unexpected saved search result')
        items = (HERE / run['log']).read_text().splitlines()[-1].split()
        stats = {items[i]: int(items[i + 1]) for i in range(0, len(items), 2)}
        require(all(run[key] == value for key, value in stats.items()),
                'saved log and JSON counter mismatch')
    baseline = read_table(HERE / 'inputs/baseline196.tm')
    cd6 = read_table(HERE / 'inputs/cd6_parent196.tm')
    cd3 = read_table(HERE / 'inputs/cd3_parent196.tm')
    labels = json.loads(re.search(r'def labels : List Nat := (\[[^\n]+\])',
                                  (HERE / 'inputs/Conjugacy.lean').read_text()).group(1))
    dense = {native: index for index, native in enumerate(labels)}
    for table, target in [(cd6, 21), (cd3, 17)]:
        differences = [row for row in baseline if baseline[row] != table[row]]
        require(differences == [(dense[27], 1)], 'parent differs in unexpected rows')
        require(table[dense[27], 1] == (1, 1, dense[target]), 'wrong zero-jump row')
    tape, state, head = set(), 0, 0
    for _ in range(58402):
        write, direction, state = cd6[state, int(head in tape)]
        if write:
            tape.add(head)
        else:
            tape.discard(head)
        head += direction
    expected = {head - 1, head, head + 48}
    cursor = head + 49
    for value in [0, 0, 0, 0, 0, 0, 2, 0, 0] + [1] * 26:
        expected.update(range(cursor + 1, cursor + value + 2))
        cursor += value + 2
    require(state == dense[84] and tape == expected, 'CD6 startup frame differs')
    first = HERE / 'results/cd6_refined/source_contexts.txt'
    second = HERE / 'results/cd6_mask_refined/source_contexts.txt'
    require(first.read_bytes() == second.read_bytes(), 'mask context file changed')
    report = json.loads((HERE / 'results/cd6_mask_refined/source_contexts_receipt.json').read_text())
    require(report['source_invariant_pairs'] == 274880
            and report['source_contracts'] == 4956
            and report['refined_windows'] == 2221, 'unexpected context receipt')
    print(json.dumps({'status': 'SAVED_ARTIFACTS_AND_EXACT_STARTUP_CHECKED',
                      'working_states': 196, 'cd6_startup_steps': 58402,
                      'source_window_files_identical': True,
                      'negative_search_runs': 3,
                      'search_rerun': False}, indent=2))

if __name__ == '__main__':
    main()
