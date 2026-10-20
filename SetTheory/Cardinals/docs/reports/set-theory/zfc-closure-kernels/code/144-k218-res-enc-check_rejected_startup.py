#!/usr/bin/env python3
"""Prove the rejected machine enters an infinite blank-tape writing ray.

Standard library only. Replay exactly 85 transitions with an unbounded sparse
binary tape, then check the single transition establishing the induction.
This is a rejection diagnostic, not a certificate for the accepted K218 table.
"""
from pathlib import Path
import argparse
import hashlib
import json

HERE = Path(__file__).resolve().parent
TABLE_SHA = '56245ec1973938193a646cbf96712aae000f1958fdcaefd197c703870c730431'
SITES_SHA = '0f6c3f9d3f0408f8d5c02d4b2f7c48a3111df4c0e24a1f1816ccab43b11d9a61'
RUNTIME_SHA = 'db4b4eb7ee7ec890ab185616654214ee5780c195ffa484f2d4e1104c8009fa18'


def need(condition, message):
    if not condition:
        raise ValueError(message)


def pinned(name, expected):
    raw = (HERE/name).read_bytes()
    need(hashlib.sha256(raw).hexdigest() == expected, 'Hash mismatch: '+name)
    return raw


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, default=HERE/'rejected_startup_receipt.json')
    args = ap.parse_args()
    raw = pinned('rejected_runtime_only_218.native.tm', TABLE_SHA)
    pinned('rejected_runtime_only_sites205.json', SITES_SHA)
    history = json.loads(pinned('rejected_runtime_only_runtime.json', RUNTIME_SHA))
    need(history['table_sha256'] == TABLE_SHA and history['sites_sha256'] == SITES_SHA,
         'Historical receipt identifies different inputs')
    need(history['status'] == 'ALL_PRIMITIVE_INTERFACES_PROVED'
         and history['cases'] == history['expected_cases'] == 6167,
         'Historical primitive-interface census differs')
    table, starts = {}, []
    for line in raw.decode('ascii').splitlines():
        if line.startswith('#! start '):
            starts.append(int(line.split()[-1]))
        elif line and not line.startswith('#'):
            q, bit, write, move, target = line.split()
            q, bit, write, target = map(int, (q, bit, write, target))
            need((q, bit) not in table and bit in (0, 1) and write in (0, 1)
                 and move in ('L', 'R'), 'Malformed transition')
            table[q, bit] = (write, -1 if move == 'L' else 1, target)
    states = {q for q, bit in table}
    need(starts == [0] and len(states) == 218 and len(table) == 436, 'Machine census')
    need(set(table) == {(q, bit) for q in states for bit in (0, 1)}, 'Partial machine')
    need(254 not in states and {z for w, d, z in table.values()}-states == {254},
         'Halting-state convention')
    q, head, ones, trace = 0, 0, set(), []
    for step in range(85):
        need(q != 254, 'Premature halt')
        bit = int(head in ones)
        write, move, target = table[q, bit]
        trace.append([step, q, head, bit, write, move, target])
        if write:
            ones.add(head)
        else:
            ones.discard(head)
        q, head = target, head+move
    need((q, head, ones) == (35, 7, {-3, -2}), 'Step 85 complete configuration differs')
    need(table[35, 0] == (1, 1, 35), 'Writing-ray transition differs')
    need(all(x < head for x in ones), 'The forward half-tape is not blank')
    # For every n>=0, the proposed configuration is:
    # q=35, h=7+n, ones={-3,-2} union {7,...,6+n}.
    # Its scanned cell 7+n is absent from the support, so 35/0 writes that cell,
    # moves to 8+n and stays in 35. This proves the n+1 case without any bound.
    receipt = {
        'status': 'PASS',
        'finding': 'REJECTED_TABLE_ENTERS_A_PROVABLY_INFINITE_WRITING_RAY',
        'table_sha256': TABLE_SHA,
        'source_sha256': SITES_SHA,
        'native_states': 218,
        'transition_rows': 436,
        'initial_configuration': {'state': 0, 'head': 0, 'one_cells': [], 'all_other_cells': 0},
        'finite_prefix': {'steps': 85, 'state': q, 'head': head,
                          'one_cells': sorted(ones), 'all_other_cells': 0,
                          'no_earlier_halt': True},
        'ray_transition': {'state': 35, 'read': 0, 'write': 1, 'move': 'R', 'next_state': 35},
        'induction': {'quantifier': 'every natural n', 'time': '85+n', 'state': 35,
                      'head': '7+n', 'one_cells': '{-3,-2} union {x in Z: 7 <= x < 7+n}',
                      'all_other_cells': 0, 'scanned_cell_is_zero': True,
                      'next_transition_establishes_n_plus_one': True,
                      'halting_state_is_never_reached': True},
        'historical_runtime_receipt': {
            'file': 'rejected_runtime_only_runtime.json', 'sha256': RUNTIME_SHA,
            'status': history['status'], 'cases': history['cases'],
            'symbolic_steps': history['symbolic_steps'],
            'scope': 'Copied earlier primitive-interface proof receipt; not rederived by this diagnostic.'},
        'trace_columns': ['step', 'state', 'head', 'read', 'write', 'move_delta', 'next_state'],
        'finite_trace': trace,
        'scope': 'Exact finite blank prefix plus elementary unbounded induction; this table is rejected and is not the accepted K218 candidate.'
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(receipt, indent=2)+'\n')
    print(json.dumps({k: receipt[k] for k in ('status', 'finding', 'table_sha256', 'finite_prefix', 'ray_transition')}, indent=2))


if __name__ == '__main__':
    main()
