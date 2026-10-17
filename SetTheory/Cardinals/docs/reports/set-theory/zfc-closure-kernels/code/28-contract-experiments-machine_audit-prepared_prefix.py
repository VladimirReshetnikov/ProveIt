#!/usr/bin/env python3
"""Finite diagnostics for the already known prepared 252-state runtime fold.

No result here is a proof of eventual halting/nonhalting or of equivalence
with ZFC. A failure to hit the published 253-state boot endpoint rules out
that particular endpoint certificate only.
"""
import hashlib
import json
from pathlib import Path
import runtime_fold_search as search


def simulate(table, start, bounds):
    head, state, ones = 0, start, set()
    snapshots = []
    for elapsed in range(max(bounds) + 1):
        if elapsed in bounds or state == '254':
            item = {'steps': elapsed, 'state_in_original254_labels': int(state),
                    'head': head, 'one_cells': sorted(ones), 'halted': state == '254'}
            item['configuration_sha256'] = hashlib.sha256(
                json.dumps(item, sort_keys=True, separators=(',', ':')).encode()).hexdigest()
            snapshots.append(item)
            if state == '254':
                break
        if elapsed == max(bounds):
            break
        write, direction, target = table[state, int(head in ones)]
        if write:
            ones.add(head)
        else:
            ones.discard(head)
        head += 1 if direction == 'R' else -1
        state = target
    return snapshots


def main():
    _, baseline, _, _ = search.load()
    original = simulate(baseline, '5', {312975})[0]
    assert original['state_in_original254_labels'] == 96
    assert original['head'] == -17 and len(original['one_cells']) == 178
    # Independently reconstruct the complete public Boot253.v frame, including
    # every spare block and the blank exterior, rather than checking a count.
    physical = [0, 2, 0, 0, 0, 0, 5, 0, 0]
    spare = [0, 0, 1, 0, 0, 0, 0, 0, 1] + [0] * 149
    expected_ones = {-18, 23}  # left marker and header at head+40
    position = 24
    for value in physical + spare:
        position += 1  # zero separator
        expected_ones.update(range(position, position + value + 1))
        position += value + 1
    assert original['one_cells'] == sorted(expected_ones)
    folded = search.FoldedTable(baseline, '5', '64', (baseline['64', 0], baseline['64', 1]))
    trials = simulate(folded, '64', {121118, 312975, 2000000})
    report = {'source_commit': search.PIN,
              'fold': {'remove': 5, 'retain': 64, 'blank_start': 64},
              'stock253_312975_step_endpoint': original,
              'prepared252_finite_snapshots': trials,
              'matches_stock253_endpoint_at312975': trials[1] == original,
              'establishes_halting_or_nonhalting': False,
              'establishes_consistency_equivalence_or_inequivalence': False,
              'scope': 'A bounded prefix diagnostic, not an initialization proof for the prepared runtime core.'}
    assert not report['matches_stock253_endpoint_at312975']
    path = Path(__file__).resolve().parent / 'prepared252-prefix.json'
    path.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'output': str(path), 'stock_endpoint_checked': True,
                      'prepared_snapshots': [{k: v for k, v in s.items() if k != 'one_cells'} | {'ones': len(s['one_cells'])}
                                            for s in trials]}, indent=2))


if __name__ == '__main__':
    main()
