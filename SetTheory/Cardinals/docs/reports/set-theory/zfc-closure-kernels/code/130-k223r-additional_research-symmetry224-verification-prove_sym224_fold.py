#!/usr/bin/env python3
"""Rebuild and certify the SYM225 -> SYM224 contextual state fold.

The finite window fixpoint is an inductive overapproximation of EVERY blank-run
configuration. It is not a bounded blank simulation. At each head movement it
introduces both possible values for the newly visible tape cell.

Each original transition is simulated by a positive finite macro of the folded
table, with exactly the same whole tape/head and the state map 600 -> 512.
The changed-state macros touch only the four cells in the proved window; all
other original states simulate in one literal transition. Consequently the two
blank runs halt together. This is an executable elementary mathematical proof,
not a proof-assistant kernel artifact.
"""
from pathlib import Path
from collections import deque
import argparse, hashlib, json

START, HALT, REMOVED, HOST = 95, 254, 600, 512
LEFT, RIGHT = 3, 0


def read(path):
    rows = {}
    for line in path.read_text().splitlines():
        if not line or line.startswith('#'):
            continue
        q, b, w, d, n = line.split()
        key = int(q), int(b)
        assert key not in rows
        rows[key] = int(w), 1 if d == 'R' else -1, int(n)
    return rows


def encode(table):
    return ('#! start 95\n' + ''.join(
        f'{q} {b} {w} {"R" if d == 1 else "L"} {n}\n'
        for (q, b), (w, d, n) in sorted(table.items()))).encode()


def relabel(q):
    return HOST if q == REMOVED else q


def build(original):
    assert original[HOST, 0] == (0, 1, 206)
    assert original[HOST, 1] == (1, 1, 244)
    assert original[REMOVED, 0] == (0, 1, 105)
    assert original[REMOVED, 1] == (1, 1, 244)
    result = {(q, b): (w, d, relabel(n))
              for (q, b), (w, d, n) in original.items() if q != REMOVED}
    result[HOST, 0] = (0, -1, 243)
    result[HOST, 1] = (1, 1, 244)
    return result


def fixpoint(table):
    width = LEFT + RIGHT + 1
    mask = (1 << width) - 1
    reached, todo = {(START, 0)}, deque([(START, 0)])
    while todo:
        q, tape = todo.popleft()
        if q == HALT:
            continue
        b = (tape >> LEFT) & 1
        w, d, n = table[q, b]
        tape = (tape & ~(1 << LEFT)) | (w << LEFT)
        for fresh in (0, 1):
            after = (tape >> 1) | (fresh << (width - 1)) if d == 1 else ((tape << 1) & mask) | fresh
            pair = n, after
            if pair not in reached:
                reached.add(pair)
                todo.append(pair)
    # The initial pair and closure under BOTH unknown boundary values prove
    # the invariant for an arbitrary number of old-machine transitions.
    assert (START, 0) in reached
    return reached


def prove_macro(original, folded, q, tape):
    initial = tape
    b = (tape >> LEFT) & 1
    w, d, n = original[q, b]
    target_tape = (tape & ~(1 << LEFT)) | (w << LEFT)
    target_head, target_state = LEFT + d, relabel(n)
    head, state, trace = LEFT, relabel(q), []
    for step in range(1, 20):
        # No symbol outside the invariant window is ever read or written.
        assert 0 <= head <= LEFT + RIGHT, (q, initial, head, state)
        read_bit = (tape >> head) & 1
        w, d, newstate = folded[state, read_bit]
        trace.append([state, head - LEFT, read_bit, w, d, newstate])
        tape = (tape & ~(1 << head)) | (w << head)
        state, head = newstate, head + d
        if (state, head, tape) == (target_state, target_head, target_tape):
            return {'old_state': q, 'window_left_to_right': ''.join(str((initial >> i) & 1) for i in range(LEFT + RIGHT + 1)),
                    'read': b, 'steps': step, 'trace': trace}
    raise AssertionError(('Macro did not close', q, initial))


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--parent', type=Path, default=Path('work/machine-search/sym225/candidate.legacy.tm'))
    ap.add_argument('--candidate', type=Path, default=Path('work/machine-search/sym224/candidate.legacy.tm'))
    ap.add_argument('--output', type=Path, default=Path('work/machine-search/sym224/fold_certificate.json'))
    args = ap.parse_args()
    original = read(args.parent)
    assert len(original) == 450 and START != HOST and START != REMOVED
    assert HALT not in {q for q, b in original}
    assert all((q, b) in original for q, _ in original for b in (0, 1))
    assert {n for w, d, n in original.values()} - {q for q, b in original} == {HALT}
    folded = build(original)
    assert len(folded) == 448
    assert folded == read(args.candidate)
    reached = fixpoint(original)
    certificates = [prove_macro(original, folded, q, tape)
                    for q, tape in sorted(reached) if q in (HOST, REMOVED)]
    assert len(certificates) == 4
    assert all(folded[q, b] == (w, d, relabel(n))
               for (q, b), (w, d, n) in original.items() if q not in (HOST, REMOVED))
    report = {'status': 'INDUCTIVE_WINDOW_AND_EXACT_MACRO_PASS',
              'parent_sha256': hashlib.sha256(args.parent.read_bytes()).hexdigest(),
              'candidate_sha256': hashlib.sha256(args.candidate.read_bytes()).hexdigest(),
              'working_states': [225, 224], 'state_map': {str(REMOVED): HOST},
              'window_offsets': [-LEFT, RIGHT], 'abstract_reachable_pairs': len(reached),
              'changed_state_macros': certificates,
              'all_other_states': 'one exact literal transition with target state map',
              'whole_tape_equality': True, 'positive_progress': True,
              'conclusion': 'The parent and candidate blank runs halt iff each other.',
              'scope': 'Finite inductive abstract interpretation and literal macro equations, formalizable in ZFC; not a proof-assistant kernel certificate.'}
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'changed_state_macros'}, indent=2))


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('Run with assertions enabled.')
    main()
