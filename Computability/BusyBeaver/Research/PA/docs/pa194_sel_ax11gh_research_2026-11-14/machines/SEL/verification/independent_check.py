#!/usr/bin/env python3
"""Independent complete certificate for the simultaneous PA194SEL rewrite.

This checker reads literal native tables. It proves the finite premises of
the all-tape simulation theorem in history_selector_proof.tex. The generic
quantifier-free induction is written there; this is not a Lean kernel.
"""
import argparse
import hashlib
import json
from pathlib import Path

PAIRS = [(12, 38, 98, 19), (127, 124, 8, 59)]
START, HALT = 74, 254


def read_table(path):
    out = {}
    for line in path.read_text().splitlines():
        if not line.strip() or line.lstrip().startswith('#'):
            continue
        q, b, w, direction, target = line.split()
        q, b, w, target = map(int, (q, b, w, target))
        assert (q, b) not in out and b in (0, 1) and w in (0, 1)
        assert direction in ('L', 'R')
        out[q, b] = (w, direction, target)
    states = {q for q, b in out}
    assert len(states) == 194 and len(out) == 388
    assert set(out) == {(q, b) for q in states for b in (0, 1)}
    assert {n for w, d, n in out.values()} - states == {HALT}
    assert START in states
    return out


def mapping(q):
    return {right: left for left, right, _, _ in PAIRS}.get(q, q)


def construction(old):
    new = {key: (w, d, mapping(target)) for key, (w, d, target) in old.items()}
    for left, right, zero_helper, one_helper in PAIRS:
        new[left, 0] = (0, 'L', right)
        new[right, 0] = (0, 'R', zero_helper)
        new[right, 1] = (1, 'R', one_helper)
    return new


def text_table(table):
    return ''.join(f'{q} {b} {w} {d} {n}\n'
                   for (q, b), (w, d, n) in sorted(table.items()))


def local_run(table, state, read, witness, length):
    cells = {-1: witness, 0: read}
    head = 0
    trace, accessed = [], set()
    for _ in range(length):
        assert state != HALT and head in cells
        accessed.add(head)
        bit = cells[head]
        w, d, target = table[state, bit]
        trace.append([state, head, bit, w, d, target])
        cells[head] = w
        head += 1 if d == 'R' else -1
        state = target
    return (state, head, cells), trace, sorted(accessed)


def blank_run(table, steps):
    state, head, ones = START, 0, set()
    hits = [0, 0]
    for _ in range(steps):
        assert state != HALT
        bit = int(head in ones)
        for i, (left, right, _, _) in enumerate(PAIRS):
            if state in (left, right) and bit == 0:
                hits[i] += 1
        w, d, state = table[state, bit]
        (ones.add if w else ones.discard)(head)
        head += 1 if d == 'R' else -1
    return (state, head, ones), hits


def check(old, new):
    assert new == construction(old), 'The proposed table has additional edits.'
    changed_labels = {q for pair in PAIRS for q in pair[:2]}
    assert len(changed_labels) == 4 and START not in changed_labels
    assert not changed_labels & {q for pair in PAIRS for q in pair[2:]}
    incoming, cases = [], []
    for left, right, helper0, helper1 in PAIRS:
        old_zero_left = old[left, 0]
        old_zero_right = old[right, 0]
        assert old_zero_left[:2] == old_zero_right[:2] == (0, 'R')
        assert old[left, 1] == old[right, 1]
        assert old[left, 1][:2] == (1, 'R')
        assert old[helper0, 0] == old_zero_left
        assert old[helper1, 0] == old_zero_right
        for q, witness in ((left, 0), (right, 1)):
            predecessors = [(key, value) for key, value in sorted(old.items()) if value[2] == q]
            assert predecessors
            assert all(value[:2] == (witness, 'R') for key, value in predecessors)
            incoming.append({'state': q, 'forced_left_bit': witness, 'predecessors': predecessors})
            for bit in (0, 1):
                before, old_trace, old_access = local_run(old, q, bit, witness, 1)
                length = 3 if bit == 0 else 1
                after, new_trace, new_access = local_run(new, mapping(q), bit, witness, length)
                assert after == (mapping(before[0]), before[1], before[2])
                assert set(new_access) <= {-1, 0}
                # Every strict block interior has a working state.
                assert all(row[0] != HALT for row in new_trace[1:])
                cases.append({'old_state': q, 'read': bit, 'left_witness': witness,
                              'new_length': length, 'old_trace': old_trace, 'new_trace': new_trace,
                              'accessed_cells': new_access, 'whole_tape_equality': True,
                              'unchanged_exterior': 'Every cell outside {-1,0} is unaccessed.'})
    changes = [[q, b, old[q, b], new[q, b]] for q, b in sorted(old) if old[q, b] != new[q, b]]
    assert len(changes) == 8 and len(cases) == 8
    old_end, old_hits = blank_run(old, 58154)
    new_length = 58154 + 2 * sum(old_hits)
    new_end, _ = blank_run(new, new_length)
    assert new_end == (mapping(old_end[0]), old_end[1], old_end[2])
    assert old_hits == [3, 24] and new_length == 58208
    assert old_end[:2] == (84, -2)
    return {'status': 'PASS', 'states': 194, 'rows': 388,
            'changes': changes, 'incoming_witnesses': incoming, 'local_cases': cases,
            'simultaneous_rewrite': True, 'helpers_unchanged': True,
            'checkpoint_map': {'38': 12, '124': 127, 'others': 'identity'},
            'witness_bounds': {'old_to_new': '3*t', 'new_to_old': 't'},
            'startup': {'old_steps': 58154, 'new_steps': new_length,
                        'old_read_zero_visits_by_pair': old_hits,
                        'state': new_end[0], 'head': new_end[1],
                        'whole_tape_equality': True, 'one_cells': sorted(new_end[2])},
            'scope': 'Complete finite premises for the all-tape theorem from start74; arbitrary initial merged/selector states are excluded unless their entry invariant is assumed.',
            'absolute_calibration': 'Inherited/open; no new PA-to-machine calibration is established.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--old', type=Path, required=True)
    parser.add_argument('--new', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--write-new', type=Path)
    args = parser.parse_args()
    if not __debug__:
        raise RuntimeError('Run with assertions enabled.')
    old = read_table(args.old)
    new = read_table(args.new) if args.new else construction(old)
    receipt = check(old, new)
    receipt['old_sha256'] = hashlib.sha256(args.old.read_bytes()).hexdigest()
    receipt['new_canonical_native_sha256'] = hashlib.sha256(text_table(new).encode()).hexdigest()
    if args.new:
        receipt['new_file_sha256'] = hashlib.sha256(args.new.read_bytes()).hexdigest()
    if args.write_new:
        args.write_new.write_text(text_table(new))
    args.output.write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({k: v for k, v in receipt.items() if k not in ('changes', 'incoming_witnesses', 'local_cases', 'startup')}, indent=2))
    print(json.dumps({'startup': {k: v for k, v in receipt['startup'].items() if k != 'one_cells'}}, indent=2))


if __name__ == '__main__':
    main()
