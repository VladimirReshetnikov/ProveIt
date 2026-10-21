#!/usr/bin/env python3
"""Finite local certificate for the CM215 proof transfer.

This checks exact tables and an invariant using every five-cell assignment,
not a blank-run sample.  The small-support locality argument connecting this
finite check to arbitrary tapes is given in CM215_transfer.md.  The separate
PositiveSimulation.lean proves the generic time-change theorem.  This script
is not itself a Lean/Rocq kernel checker.
"""
import argparse
import hashlib
import itertools
import json
from pathlib import Path

OLD_HASH = '9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2'
NEW_HASH = 'e5907f08e0752eada0e25bbf33680341e80e5fe94b52b409aea1ed039edda252'
HALT = 254

def parse(path):
    data = path.read_bytes()
    table = {}
    start = None
    for line in data.decode().splitlines():
        if line.startswith('#! start '):
            start = int(line.split()[-1])
        elif line and not line.startswith('#'):
            q, b, w, d, z = line.split()
            q, b, w, z = map(int, (q, b, w, z))
            assert b in (0, 1) and w in (0, 1) and d in ('L', 'R')
            assert (q, b) not in table
            table[q, b] = (w, -1 if d == 'L' else 1, z)
    return start, table, hashlib.sha256(data).hexdigest()

def phi(q):
    return 52 if q == 176 else q

def invariant(q, h, tape):
    return ((q != 52 or tape[h - 1] == 1)
            and (q != 176 or tape[h] == 1 or tape[h - 1] == 0)
            and (q != 156 or tape[h + 1] == 1))

def step(table, q, h, tape):
    if q == HALT:  # Totalization used by PositiveSimulation.lean.
        return q, h, tape.copy()
    assert h in tape, 'The proof fragment inspected an unspecified outside cell'
    w, d, z = table[q, tape[h]]
    result = tape.copy()
    result[h] = w
    return z, h + d, result

def check(old_path, new_path):
    start, old, old_hash = parse(old_path)
    nstart, new, new_hash = parse(new_path)
    assert old_hash == OLD_HASH and new_hash == NEW_HASH
    assert start == nstart == 0
    assert old.keys() == new.keys()
    states = sorted({q for q, b in old})
    assert len(states) == 215 and len(old) == len(new) == 430
    assert set(old) == {(q, b) for q in states for b in (0, 1)}
    assert HALT not in states
    for table in (old, new):
        assert {z for w, d, z in table.values()} <= set(states) | {HALT}

    incoming = lambda q: {str(k): a for k, a in old.items() if a[2] == q}
    changes = [{'state': q, 'read': b, 'old': old[q, b], 'new': new[q, b]}
               for q, b in sorted(old) if old[q, b] != new[q, b]]
    assert len(changes) == 6
    checked = omitted = long_blocks = 0
    for q in states + [HALT]:
        for bits in itertools.product((0, 1), repeat=5):
            tape = dict(zip(range(-2, 3), bits))
            if not invariant(q, 0, tape):
                omitted += 1
                continue
            checked += 1
            oq, oh, otape = step(old, q, 0, tape)
            assert invariant(oq, oh, otape)
            assert (q == HALT) == (phi(q) == HALT)
            k = 3 if q in (52, 176) and tape[0] == 0 else 1
            long_blocks += (k == 3)
            nq, nh, ntape = phi(q), 0, tape.copy()
            for _ in range(k):
                nq, nh, ntape = step(new, nq, nh, ntape)
            assert (nq, nh, ntape) == (phi(oq), oh, otape), (q, bits)
    assert all(invariant(0, 0, dict(zip(range(-2, 3), bits)))
               for bits in itertools.product((0, 1), repeat=5))
    return {
        'status': 'PASS',
        'scope': 'Exhaustive finite local hypotheses; global all-tape induction is in the report',
        'old_sha256': old_hash, 'new_sha256': new_hash,
        'working_states': 215, 'rows': 430,
        'window_offsets': [-2, -1, 0, 1, 2],
        'local_assignments_total': (len(states) + 1) * 32,
        'invariant_compatible_assignments_checked': checked,
        'incompatible_assignments_excluded_by_inductive_invariant': omitted,
        'three_step_blocks_checked': long_blocks,
        'initial_invariant_assignments': 32,
        'changed_rows': changes,
        'incoming_52': incoming(52),
        'incoming_176': incoming(176),
        'incoming_156': incoming(156),
        'invariant': [
            'q = 52 implies tape[h-1] = 1',
            'q = 176 and tape[h] = 0 imply tape[h-1] = 0',
            'q = 156 implies tape[h+1] = 1'],
        'generic_lean_theorem': 'PositiveSimulation.halts_iff',
        'exact_table_lean_endpoint': 'Not claimed by this Python certificate'
    }

if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--old', type=Path, default=Path(__file__).with_name('k215.native.tm'))
    p.add_argument('--new', type=Path, default=Path(__file__).with_name('cm215.native.tm'))
    p.add_argument('--out', type=Path, default=Path(__file__).with_name('marker-certificate.json'))
    a = p.parse_args()
    result = check(a.old, a.new)
    a.out.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: result[k] for k in ['status', 'working_states', 'rows',
        'local_assignments_total', 'invariant_compatible_assignments_checked',
        'three_step_blocks_checked']}, indent=2))
