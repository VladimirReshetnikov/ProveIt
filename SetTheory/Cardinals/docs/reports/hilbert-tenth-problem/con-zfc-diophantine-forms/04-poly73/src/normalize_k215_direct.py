#!/usr/bin/env python3
"""Explicit stay-first, two-sided K215 normalizer for fixed unary input.

The exact helical local rules allow arbitrary right and left blank margins.
Thus a folded one-sided simulation is unnecessary: initialization erases all
unary input and starts the literal 215-state table on a blank two-sided tape.
This has 219 working states, one absorbing halt, and three tape symbols.
See DIRECT_NORMALIZER_PROOF.md for the two-margin completeness argument.
"""

from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path

SOURCE_SHA256 = 'fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090'
SOURCE_COMMIT = 'cdd582bec13f908df3711fa9e05d1ddac368a5db'
START, FIRST, ERASE, RETURN = 0, 1, 2, 3
HALT = 219


def load_source(path):
    # Only trailing empty lines introduced by text transport are ignored.
    raw = Path(path).read_bytes().rstrip(b'\n') + b'\n'
    if hashlib.sha256(raw).hexdigest() != SOURCE_SHA256:
        raise ValueError('K215 source table does not match the pinned release')
    table = {}
    for line in raw.decode('ascii').splitlines():
        if not line or line.startswith('#'):
            continue
        q, r, w, direction, n = line.split()
        key = int(q), int(r)
        if key in table:
            raise ValueError('duplicate K215 transition')
        table[key] = int(n), int(w), {'L': -1, 'R': 1}[direction]
    if set(table) != {(q, r) for q in range(215) for r in range(2)}:
        raise ValueError('K215 transition domain is not exactly 215 x 2')
    if any(n not in range(216) or w not in (0, 1) for n, w, _ in table.values()):
        raise ValueError('K215 transition codomain is malformed')
    return table


def simstate(q):
    return q + 4


def normalized_table(source):
    # All unused inputs loop without accepting. The halt is absorbing.
    table = {(q, a): (q, a, 0) for q in range(HALT + 1) for a in range(3)}
    table[START, 1] = FIRST, 2, 0
    table[FIRST, 2] = ERASE, 2, -1
    table[ERASE, 1] = ERASE, 0, -1
    table[ERASE, 0] = RETURN, 0, 1
    table[RETURN, 0] = RETURN, 0, 1
    table[RETURN, 2] = simstate(0), 0, 0
    for (q, read), (nq, write, move) in source.items():
        table[simstate(q), read] = simstate(nq), write, move
    return table


def document(source):
    table = normalized_table(source)
    return {
        'format': 'two-sided-stay-first-tm-v1',
        'source_commit': SOURCE_COMMIT,
        'source_sha256': SOURCE_SHA256,
        'states': list(range(HALT + 1)),
        'alphabet': list(range(3)),
        'start': START, 'first_state': FIRST, 'halt': HALT, 'blank': 0,
        'head_origin': 0,
        'initial_input': 'ones on -(y+1), ..., 0; the fixed input is y=2',
        'transition_columns': ['state', 'read', 'next', 'write', 'move'],
        'move_convention': '-1 left; 0 stay; +1 right',
        'working_states': HALT, 'total_states': HALT + 1,
        'normalization_theorem': 'For every y>=1, the machine accepts its y+2 unary ones iff K215 halts on the blank tape.',
        'helical_padding': 'Both blank margins are chosen after the finite run; see DIRECT_NORMALIZER_PROOF.md.',
        'transitions': [[q, a, n, w, d] for (q, a), (n, w, d)
                        in sorted(table.items())],
    }


def step(table, state, head, tape):
    ns, write, move = table[state, tape.get(head, 0)]
    if write:
        tape[head] = write
    else:
        tape.pop(head, None)
    return ns, head + move


def verify(source, steps=120000):
    table = normalized_table(source)
    if set(table) != {(q, a) for q in range(220) for a in range(3)}:
        raise ValueError('normalized table is incomplete')
    if table[START, 1] != (FIRST, 2, 0):
        raise ValueError('first-step contract failed')
    if any(table[HALT, a] != (HALT, a, 0) for a in range(3)):
        raise ValueError('halt is not absorbing')
    for (q, read), (nq, write, move) in source.items():
        if table[simstate(q), read] != (simstate(nq), write, move):
            raise ValueError('literal transition relabeling failed')
    init_cases = []
    for length in (2, 3, 4, 5, 10, 31):
        tape = {-j: 1 for j in range(length)}
        q, h, count = START, 0, 0
        while q != simstate(0):
            q, h = step(table, q, h, tape)
            count += 1
            if count > 2*length+2:
                raise ValueError('input erasure failed')
        if (h, tape, count) != (0, {}, 2*length+2):
            raise ValueError('input erasure did not produce the blank tape')
        init_cases.append({'ones': length, 'steps': count})
    original, normalized = {}, {}
    oq, oh, nq, nh = 0, 0, simstate(0), 0
    done = 0
    while done < steps and oq != 215:
        oq, oh = step(source, oq, oh, original)
        nq, nh = step(table, nq, nh, normalized)
        if (nq, nh) != (simstate(oq), oh):
            raise ValueError('paired run state/head mismatch')
        done += 1
    if normalized != original:
        raise ValueError('paired run final tape mismatch')
    return {
        'source_commit': SOURCE_COMMIT,
        'source_sha256': SOURCE_SHA256,
        'working_states': 219, 'total_states': 220,
        'tape_symbols': 3, 'transition_rows': 660,
        'literal_source_rows_checked': len(source),
        'unary_erasure_cases': init_cases,
        'paired_blank_steps': done, 'observed_halt': oq == 215,
        'proof_status': 'Hand proof with finite executable checks; no Lean or Rocq proof of this normalization is supplied.',
        'meaning': 'The finite prefix is not evidence of unconditional nonhalting.',
    }


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('source', type=Path)
    p.add_argument('--output', type=Path)
    p.add_argument('--verify', action='store_true')
    p.add_argument('--receipt', type=Path)
    args = p.parse_args()
    source = load_source(args.source)
    if args.output:
        args.output.write_text(json.dumps(document(source), indent=2)+'\n')
    if args.verify or args.receipt:
        report = verify(source)
        if args.receipt:
            args.receipt.write_text(json.dumps(report, indent=2)+'\n')
        print(json.dumps(report, indent=2))
    elif not args.output:
        print(json.dumps(document(source), indent=2))


if __name__ == '__main__':
    main()
