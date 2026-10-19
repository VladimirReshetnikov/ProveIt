#!/usr/bin/env python3
"""Verify the previously reported 235->98 reduction from exact238 to exact237.

This is an independent ordinary mathematical certificate, using only the
Python standard library.  The invariant is inductive from state95 for EVERY
binary initial tape. Three exact finite blocks never inspect unspecified tape
cells. All other old rows agree in one step under phi(235)=98. Thus no source
runtime guard or finite-run extrapolation enters this additional reduction.

The reduction is credited to the earlier report
ZFC_237_State_Construction_2026-10-19.pdf; this script is an independent replay,
not a claim to discovery of that reduction.
"""
import argparse
import hashlib
import json
from pathlib import Path

START, HALT = 95, 254
BASE_SHA256 = '069942be27db9736875ea042320e51ac3b1eac7116cbe01cdce520fa6056f78c'
INHERITED_SHA256 = 'a3c4407f30e2e2139af87c6a91948c518134855841a28eb85b1d81bcfd026c9a'
CANONICAL_SHA256 = '7eda1da1fcda629cae86d22b01d3faf419552cf04ed4179f0c045ad0adf2c1a6'


def require(test, message):
    if not test:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    rows = {}
    for number, line in enumerate(path.read_text().splitlines(), 1):
        if not line or line.startswith('#'):
            continue
        fields = line.split()
        require(len(fields) == 5, f'Invalid row at line{number}')
        q, b, w, d, n = fields
        q, b, w, n = map(int, (q, b, w, n))
        require(q >= 0 and n >= 0 and b in (0, 1) and w in (0, 1) and d in ('L', 'R'), 'Invalid transition')
        require((q, b) not in rows, 'Duplicate transition')
        rows[q, b] = w, (1 if d == 'R' else -1), n
    states = {q for q, _ in rows}
    require(set(rows) == {(q, b) for q in states for b in (0, 1)}, 'Incomplete binary table')
    require(START in states and HALT not in states, 'Wrong inherited start or halt convention')
    require({n for _, _, n in rows.values()} - states == {HALT}, 'Wrong exit state')
    return rows


def phi(q):
    return 98 if q == 235 else q


def construct(old):
    new = {(q, b): (w, d, phi(n)) for (q, b), (w, d, n) in old.items() if q != 235}
    new[98, 0] = (0, -1, 240)
    new[240, 1] = (1, -1, 87)
    return new


def serialize(rows, start):
    return f'#! start {start}\n' + ''.join(
        f'{q} {b} {w} {"R" if d == 1 else "L"} {n}\n'
        for (q, b), (w, d, n) in sorted(rows.items()))


def canonicalize(rows):
    working = {q for q, _ in rows}
    order = [START] + sorted(working - {START})
    forward = {q: i for i, q in enumerate(order)}
    forward[HALT] = len(order)
    canonical = {(forward[q], b): (w, d, forward[n]) for (q, b), (w, d, n) in rows.items()}
    require(set(canonical) == {(q, b) for q in range(237) for b in (0, 1)}, 'Wrong canonical domain')
    require(forward[START] == 0 and forward[HALT] == 237, 'Wrong canonical start or halt')
    for (q, b), (w, d, n) in rows.items():
        require(canonical[forward[q], b] == (w, d, forward[n]), 'Relabeling is not action preserving')
    return canonical, forward


def run(rows, initial_state, assumptions, length):
    state, head, tape, trace = initial_state, 0, dict(assumptions), []
    for tick in range(length):
        require(head in tape, f'Unknown exterior bit scanned at state{state}, relative cell{head}')
        require(state != HALT, 'Intermediate halt')
        bit = tape[head]
        write, direction, target = rows[state, bit]
        trace.append({'state': state, 'head': head, 'read': bit, 'write': write,
                      'direction': direction, 'target': target})
        tape[head] = write
        state, head = target, head + direction
    require(state != HALT, 'Exceptional block endpoint must be a working state')
    return (state, head, tape), trace


def verify(old, new):
    old_states, new_states = {q for q, _ in old}, {q for q, _ in new}
    require(len(old_states) == 238 and len(new_states) == 237, 'Wrong state counts')
    require(new_states == old_states - {235}, 'Wrong removed state')
    require(new == construct(old), 'Candidate differs from certified edits')
    require(old[235, 0] == (0, 1, 231) and old[235, 1] == (1, 1, 16), 'Wrong removed rows')
    require(old[98, 0] == (0, 1, 113) and old[98, 1] == (1, 1, 16), 'Wrong old98 rows')
    require(old[240, 1] == (1, 1, 99), 'Wrong old240 row')
    inv = {98: {-1: 0}, 139: {-1: 1}, 156: {-1: 1}, 235: {-2: 1, -1: 1}, 240: {-1: 0}}
    require(START not in inv, 'Invariant must be vacuous at initial state')
    preservation = []
    for (q, b), (w, d, n) in sorted(old.items()):
        if n not in inv:
            continue
        source = dict(inv.get(q, {}))
        source[0] = w
        obligations = [[offset, value, offset + d, source.get(offset + d)]
                       for offset, value in inv[n].items()]
        require(all(wanted == actual for _, wanted, _, actual in obligations),
                f'Structural invariant failed on incoming row{q}/{b}')
        preservation.append({'row': [q, b], 'target': n, 'shifted_bit_implications': obligations})
    incoming235 = sorted([list(k) for k, (_, _, n) in old.items() if n == 235])
    require(incoming235 == [[139, 1], [156, 1]], 'Additional old235 caller')

    specs = [
        (98, {-1: 0, 0: 0}, 1, 3, 113),
        (235, {-2: 1, -1: 1, 0: 0}, 1, 5, 231),
        (240, {-1: 0, 0: 1}, 1, 3, 99),
    ]
    cases = []
    for q, assumptions, old_steps, new_steps, endpoint in specs:
        before, old_trace = run(old, q, assumptions, old_steps)
        after, new_trace = run(new, phi(q), assumptions, new_steps)
        require(before[0] == after[0] == endpoint, 'Unexpected endpoint control')
        require(before[1] == after[1] == 1, 'Unexpected endpoint head')
        for p in before[2].keys() | after[2].keys():
            free = ('arbitrary_original_bit', p)
            require(before[2].get(p, free) == after[2].get(p, free), 'Unequal whole tapes')
        require(before[2] == assumptions and after[2] == assumptions, 'A block changed the tape')
        cases.append({'old_state': q, 'new_state': phi(q), 'assumptions': assumptions,
                      'old_steps': old_steps, 'new_steps': new_steps,
                      'endpoint_state': endpoint, 'endpoint_head': 1,
                      'whole_tape_unchanged': True, 'old_trace': old_trace, 'new_trace': new_trace})
    exceptional = {(98, 0), (235, 0), (240, 1)}
    ordinary = []
    for (q, b), (w, d, n) in sorted(old.items()):
        if (q, b) in exceptional:
            continue
        require(new[phi(q), b] == (w, d, phi(n)), f'Ordinary row disagrees at{q}/{b}')
        ordinary.append([q, b])
    require(len(ordinary) == 473 and len(ordinary) + len(cases) == len(old) == 476,
            'Incomplete old-row coverage')
    changed = [{'row': list(k), 'old': old.get(k), 'new': new.get(k)}
               for k in sorted(old.keys() | new.keys()) if old.get(k) != new.get(k)]
    return {'status': 'EXACT237_ALL_INITIAL_TAPE_BLOCK_SIMULATION_PASS',
            'working_states': [238, 237], 'rows': [476, 474],
            'start': START, 'halt': HALT, 'deleted_state': 235,
            'state_map': '235 -> 98; all other labels fixed',
            'initial_tapes': 'Every binary tape indexed by the integers at start95',
            'extra_semantic_guard': None, 'structural_invariant': inv,
            'invariant_preservation_rows': preservation, 'incoming235': incoming235,
            'exceptional_cases': cases, 'ordinary_rows_checked': len(ordinary),
            'ordinary_rows': ordinary, 'complete_old_row_coverage': len(old),
            'changed_rows': changed, 'maximum_new_block_steps': 5,
            'proof': 'The invariant is vacuous at95 and is preserved by every incoming transition. Map old235 to98. Every old row is simulated by a positive finite new block, with identical entire tape and head and mapped control. Three exceptional rows use checked blocks of lengths3,5,3;473 other rows use one step. No exceptional block contains a halt. Induction gives matching checkpoints for every old step. Thus finite old halting implies finite new halting, and an infinite old run gives an infinite new run with unbounded accumulated time. Determinism gives halting equivalence for every initial tape.',
            'attribution': 'Additional235->98 reduction from the prior ZFC_237_State_Construction_2026-10-19.pdf; independent replay and certificate prepared here.',
            'proof_scope': 'Ordinary finite mathematical certificate; no proof-assistant kernel endpoint asserted.'}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--old', type=Path, required=True)
    ap.add_argument('--new', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--build', action='store_true', help='Write inherited and canonical tables before checking; all paths must be new')
    args = ap.parse_args()
    require(digest(args.old) == BASE_SHA256, 'Wrong exact238 predecessor bytes')
    old = read(args.old)
    canonical_path = args.new.with_name('zfc_extended237.tm')
    renumbering_path = args.new.with_name('renumbering237.json')
    if args.build:
        require(not args.new.exists() and not canonical_path.exists() and not renumbering_path.exists(), 'Build destinations must be new')
        new = construct(old)
        verify(old, new)
        canonical, forward = canonicalize(new)
        args.new.write_text(serialize(new, START))
        canonical_path.write_text(serialize(canonical, 0))
        renumbering_path.write_text(json.dumps({'start': 0, 'halt': 237, 'old_to_new': forward}, indent=2) + '\n')
    new = read(args.new)
    result = verify(old, new)
    canonical, forward = canonicalize(new)
    result.update(old_sha256=digest(args.old), new_sha256=digest(args.new),
                  canonical_sha256=hashlib.sha256(serialize(canonical, 0).encode()).hexdigest(),
                  canonical_start=0, canonical_halt=237, canonical_dispatch=forward[96],
                  verifier_sha256=digest(Path(__file__)))
    require(result['new_sha256'] == INHERITED_SHA256, 'Inherited bytes differ from prior reported237 identity')
    require(result['canonical_sha256'] == CANONICAL_SHA256, 'Canonical bytes differ from prior reported237 identity')
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: result[k] for k in ('status', 'working_states', 'rows', 'ordinary_rows_checked', 'old_sha256', 'new_sha256', 'canonical_sha256', 'extra_semantic_guard')}, indent=2))


if __name__ == '__main__':
    main()
