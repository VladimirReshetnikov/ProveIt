#!/usr/bin/env python3
"""Reprove the delayed-erasure fold on the independently supplied Boundary239.

The local proofs use distinct symbolic bits for all unspecified tape cells.
The invariant is established by the exact incoming transition rows.  The
nonlocal right-neighbor guard is checked on the complete blank prefix here,
and on all arbitrary-parameter runtime frames by verify_guard238.py.

This finite mathematical verifier is independent of the symbolic runtime
engine.  It does not decide the consistency of ZFC.
"""
from pathlib import Path
from collections import Counter
import argparse
import hashlib
import json
import sys

BASE_SHA = 'd061770f487937f9da652919c9bc9bb79bc9bf137ca41dd7a08eb5ecda8e7719'
NEW_SHA = '069942be27db9736875ea042320e51ac3b1eac7116cbe01cdce520fa6056f78c'
BOOT_STEPS = 409691
PREDICATE = {
    67: {-1: 0},
    80: {-2: 0, -1: 1},
    91: {-3: 0, -2: 1, -1: 1},
    169: {-1: 0},
}
SPECS = [
    (80, 0, {-1: 1, 0: 0}, 5, [80, 106, 92, 107, 125, 25]),
    (169, 0, {-1: 0, 0: 0}, 3, [80, 106, 93, 57]),
    (169, 1, {-1: 0, 0: 1, 1: 1}, 5, [80, 91, 167, 151, 173, 56]),
    (91, 1, {-3: 0, -2: 1, -1: 1, 0: 1}, 9,
     [91, 167, 151, 24, 36, 54, 71, 82, 94, 50]),
]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def parse(path, inherited_start=None):
    table, start = {}, None
    for line in path.read_text(encoding='ascii').splitlines():
        if line.startswith('#! start '):
            assert start is None
            start = int(line.split()[-1])
        elif line and not line.startswith('#'):
            q, b, w, d, z = line.split()
            q, b, w, z = map(int, (q, b, w, z))
            assert (q, b) not in table
            assert b in (0, 1) and w in (0, 1) and d in ('L', 'R')
            table[q, b] = (w, -1 if d == 'L' else 1, z)
    if start is None:
        assert inherited_start is not None, 'A header or explicit start convention is required'
        start = inherited_start
    states = {q for q, _ in table}
    assert start in states
    assert set(table) == {(q, b) for q in states for b in (0, 1)}
    assert {z for _, _, z in table.values()} - states == {254}
    return start, table


def phi(q):
    return 80 if q == 169 else q


def initial_bit(tape, position):
    return tape.get(position, ('independent_original_bit', position))


def run_open(table, state, assumptions, steps):
    tape, head, trace = dict(assumptions), 0, []
    for _ in range(steps):
        assert state != 254, 'Interior halt in a local block'
        b = initial_bit(tape, head)
        assert b in (0, 1), ('Unconstrained read', state, head, b)
        w, d, z = table[state, b]
        trace.append([state, head, b, w, d, z])
        tape[head] = w
        state, head = z, head + d
    return state, head, tape, trace


def literal(table, q, h, ones):
    w, d, z = table[q, int(h in ones)]
    if w:
        ones.add(h)
    else:
        ones.discard(h)
    return z, h + d


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--baseline', type=Path, required=True)
    ap.add_argument('--candidate', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    assert __debug__ and not sys.flags.optimize
    assert digest(args.baseline) == BASE_SHA
    assert digest(args.candidate) == NEW_SHA
    # The pinned Boundary239 old-label file has no header; its documented
    # inherited start convention is 95. The new file declares its own start.
    os, old = parse(args.baseline, inherited_start=95)
    ns, new = parse(args.candidate)
    assert (os, ns, len(old), len(new)) == (95, 95, 478, 476)
    expected = {(q, b): (w, d, phi(z))
                for (q, b), (w, d, z) in old.items() if q != 169}
    expected[80, 0] = (0, -1, 106)
    expected[91, 1] = (1, -1, 167)
    assert new == expected
    edits = [[q, b, list(old[q, b]), list(new[q, b])]
             for q, b in sorted(new) if old[q, b] != new[q, b]]
    assert [x[:2] for x in edits] == [[80, 0], [91, 1], [147, 0]]

    # The assertion is initially vacuous at q95, for every entire tape.
    assert 95 not in PREDICATE
    incoming_proofs = []
    for (q, b), (w, d, z) in sorted(old.items()):
        if z not in PREDICATE:
            continue
        before = {**PREDICATE.get(q, {}), 0: b}
        after = {**before, 0: w}
        for offset, required in PREDICATE[z].items():
            assert after.get(offset + d) == required, (q, b, z, offset)
        incoming_proofs.append({'row': [q, b, w, d, z], 'known_after': after})

    blocks = []
    exceptional = set()
    for q, b, assumptions, n, path in SPECS:
        exceptional.add((q, b))
        oq, oh, ot, old_trace = run_open(old, q, assumptions, 1)
        nq, nh, nt, new_trace = run_open(new, phi(q), assumptions, n)
        assert (nq, nh) == (phi(oq), oh)
        for p in ot.keys() | nt.keys():
            assert initial_bit(ot, p) == initial_bit(nt, p), (q, b, p)
        assert [row[0] for row in new_trace] + [nq] == path
        assert nq != 254
        blocks.append({'old_state': q, 'read': b, 'assumptions': assumptions,
                       'old_steps': 1, 'new_steps': n, 'old_trace': old_trace,
                       'new_trace': new_trace, 'endpoint': [nq, nh],
                       'arbitrary_exterior': True})
    ordinary = 0
    for (q, b), (w, d, z) in old.items():
        if (q, b) in exceptional:
            continue
        assert new[phi(q), b] == (w, d, phi(z))
        ordinary += 1
    assert ordinary == 474

    # At each old step, compare the exact full new tape at the corresponding
    # positive-block checkpoint. Equality of sparse supports includes zero
    # cells outside both finite supports.
    qo = qn = 95
    ho = hn = 0
    to, tn = set(), set()
    costs = {(q, b): n for q, b, _, n, _ in SPECS}
    counts = Counter()
    nextone = []
    newsteps = 0
    for tick in range(BOOT_STEPS):
        assert (phi(qo), ho, to) == (qn, hn, tn), ('before', tick)
        for offset, required in PREDICATE.get(qo, {}).items():
            assert int(ho + offset in to) == required
        key = qo, int(ho in to)
        if key == (169, 1):
            assert ho + 1 in to, ('next-one', tick, ho)
            nextone.append([tick, ho])
        n = costs.get(key, 1)
        counts[key] += 1
        qo, ho = literal(old, qo, ho, to)
        for _ in range(n):
            qn, hn = literal(new, qn, hn, tn)
        newsteps += n
        assert (phi(qo), ho, to) == (qn, hn, tn), ('after', tick)
    assert (qo, ho, len(to)) == (96, -5, 351)
    assert newsteps == 409835
    assert newsteps == BOOT_STEPS + sum((n - 1) * counts[q, b]
                                       for q, b, _, n, _ in SPECS)
    answer = {
        'status': 'INDEPENDENT_BOUNDARY239_TO_COMBINED238_LOCAL_PASS',
        'baseline_sha256': BASE_SHA, 'candidate_sha256': NEW_SHA,
        'checker_sha256': digest(Path(__file__)),
        'working_states_before': 239, 'working_states_after': 238,
        'changed_retained_rows': edits,
        'deleted_state': 169, 'mapped_state': 80,
        'structural_invariant': PREDICATE,
        'invariant_initial_tape': 'arbitrary',
        'invariant_incoming_proofs': incoming_proofs,
        'ordinary_commuting_rows': ordinary,
        'exceptional_blocks': blocks,
        'old_to_new_step_bounds': [1, 9],
        'boot': {'old_steps': BOOT_STEPS, 'new_steps': newsteps,
                 'full_checkpoints': BOOT_STEPS + 1,
                 'exceptional_visits': {f'{q}/{b}': counts[q, b]
                                        for q, b in sorted(exceptional)},
                 'next_one_visits': nextone, 'final_state': qo,
                 'final_head': ho, 'all_one_positions': sorted(to),
                 'all_other_cells_zero': True},
        'remaining_premise': 'Every Boundary239 runtime q169/read1 has a one immediately right; prove with verify_guard238.py.',
        'conclusion': 'Conditional on that separately proved runtime premise, positive finite block simulation preserves the entire tape, head, and halting equivalence. The structural invariant concerns old configurations only.',
        'halting_argument': 'Each old step maps to 1..9 new steps with no intermediate halt; unchanged halt-entering steps map exactly. Thus finite halting and infinite execution transfer. Determinism identifies the mapped execution with the unique new run.',
        'scope': 'Ordinary mathematical finite verification, with symbolic arbitrary exterior tapes; no proof-assistant kernel endpoint is claimed.',
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(answer, indent=2) + '\n')
    print(json.dumps({k: v for k, v in answer.items()
                      if k not in ('exceptional_blocks', 'invariant_incoming_proofs', 'boot')}, indent=2))
    print(json.dumps({k: v for k, v in answer['boot'].items()
                      if k != 'all_one_positions'}, indent=2))


if __name__ == '__main__':
    main()
