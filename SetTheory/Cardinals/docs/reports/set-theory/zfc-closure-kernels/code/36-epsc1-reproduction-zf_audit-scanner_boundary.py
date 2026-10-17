#!/usr/bin/env python3
"""Check the decoder/scanner boundary of the pinned public ZFC253 machine.

This original diagnostic consumes, but does not modify, the attributed
Mira-Cult / mira-emmy / Jeffrey / Wade machine and Coq program. It uses
independent parsers and literal finite simulations; no Coq or Lean proof
is claimed. Run with Python 3, assertions enabled:

  python scanner_boundary.py zfc_253.tm Prog254.v --output scanner_boundary.json

The source tree is mira-emmy/busy-beaver commit
0d544f2a2e3c18f12278441a74b7879f31cbe856, ZF/m253/machine/zfc_253.tm and
ZF/m254/coq/tm/Prog254.v. The program is inherited unchanged from M254.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import sys

TABLE_SHA = '84a21f714017c1d491008d86e9bd19c43cc6c5c9ae99a538b4f2314387827d95'
PROG_SHA = '1fbc30fcf82a1442ed88d1a1dde412630a431d32a7265d22bdf8517bffe01746'
PIN = '0d544f2a2e3c18f12278441a74b7879f31cbe856'


def read_pinned(path, digest):
    data = path.read_bytes()
    if hashlib.sha256(data).hexdigest() != digest:
        raise ValueError(f'Unexpected SHA256 for {path}')
    return data.decode('utf-8')


def table(text):
    rows = {}
    assert text.startswith('#! start 0\n')
    for line in text.splitlines():
        if not line or line.startswith('#'):
            continue
        q, bit, write, direction, target = line.split()
        key = int(q), int(bit)
        assert key not in rows and direction in ('L', 'R')
        rows[key] = int(write), 1 if direction == 'R' else -1, int(target)
    assert set(rows) == {(q, b) for q in range(253) for b in (0, 1)}
    assert all(w in (0, 1) and 0 <= q <= 253 for w, d, q in rows.values())
    return rows


def program(text):
    body = text.split('Definition p254_tab : list (cedge * cedge) := [', 1)[1].split('].', 1)[0]
    nodes = re.findall(r'\((C[NIDBC] \d+|CH), (C[NIDBC] \d+|CH)\)', body)
    assert len(nodes) == 6459
    leaves = []
    seen = set()

    def visit(index, word):
        assert index not in seen
        seen.add(index)
        for bit, edge in enumerate(nodes[index]):
            path = word + str(bit)
            if edge.startswith('CN '):
                child = int(edge[3:])
                assert index < child < len(nodes)
                visit(child, path)
            else:
                leaves.append((path, edge))

    visit(0, '')
    assert len(seen) == 6459 and len(leaves) == 6460
    return leaves


def strip(bit, count, pc):
    while count and pc:
        count -= pc[-1] == bit
        pc = pc[:-1]
    return pc


def increment(pc):
    if '0' not in pc:
        return '', 1
    at = pc.rindex('0')
    return pc[:at] + '1', 0


def rm_witness(leaves):
    lookup = {path: (i, op) for i, (path, op) in enumerate(leaves)}
    registers, pc, gap = [2, 0, 0, 0, 0, 0, 0, 0, 0], '', 37
    # The complete public Boot253 frame is at RM step 330. Its two nonzero
    # spare values are retained; later positive decrements append zero blocks.
    spare = [0] * 158
    spare[2] = spare[8] = 1
    records = []
    for step in range(1042):
        path = pc
        while path not in lookup:
            path += '0'
        index, op = lookup[path]
        if step < 1041:
            assert '0000000' not in path
        if step in (0, 330, 1041):
            records.append(dict(step=step, pc=pc, path=path, registers=registers[:],
                                gap=gap, leaf_index=index, operation=op))
        if step == 330:
            assert registers == [5, 0, 0, 0, 2, 0, 0, 0, 0]
            assert pc == '' and gap == 40
        if step == 1041:
            assert index == 41 and op == 'CD 1' and registers[1] == 0
            assert registers == [7, 0, 0, 0, 2, 0, 0, 0, 0] and gap == 42
            return records, spare
        assert op != 'CH'
        arg = int(op[3:])
        overflow = 0
        if op.startswith('CI'):
            registers[arg] += 1
            pc, overflow = increment(path)
        elif op.startswith('CD'):
            if registers[arg]:
                registers[arg] -= 1
                if step >= 330:
                    spare.append(0)
                pc, overflow = increment(path)
            else:
                pc, overflow = increment(strip('0', 1, path))
        elif op.startswith('CB'):
            pc, overflow = increment(strip('0', arg, path))
        elif op.startswith('CC'):
            pc = strip('1', arg, path)
        else:
            raise ValueError(op)
        gap += overflow


def frame(pc, gap, registers, spare, header=23):
    head = header - gap
    ones = {head - 1, header}
    ones.update(head + i for i, bit in enumerate(pc) if bit == '1')
    physical = [registers[i] for i in [2, 4, 3, 7, 6, 8, 0, 1, 5]]
    at = header + 1
    for value in physical + spare:
        ones.update(range(at + 1, at + value + 2))
        at += value + 2
    return 33, head, ones


def run_to(rows, initial, target, fuel):
    q, head, ones0 = initial
    ones = ones0.copy()
    tq, th, tone = target
    lo = hi = head
    for step in range(fuel + 1):
        if step and q == tq and head == th and ones == tone:
            return dict(status='reached', steps=step, min_head=lo, max_head=hi)
        if step == fuel:
            return dict(status='limit', steps=step, state=q, head=head,
                        ones_count=len(ones))
        if q == 253:
            return dict(status='halt', steps=step)
        write, move, q = rows[q, int(head in ones)]
        if write:
            ones.add(head)
        else:
            ones.discard(head)
        head += move
        lo, hi = min(lo, head), max(hi, head)


def main():
    if sys.flags.optimize:
        raise RuntimeError('Run with assertions enabled')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('machine', type=Path)
    parser.add_argument('program', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    rows = table(read_pinned(args.machine, TABLE_SHA))
    leaves = program(read_pinned(args.program, PROG_SHA))
    zero_runs = Counter(max(map(len, p.split('1'))) for p, _ in leaves)
    critical = [(i, p, o) for i, (p, o) in enumerate(leaves) if '0000000' in p]
    assert len(critical) == 18
    assert all(p.endswith('0000000') and o.startswith('CD') for i, p, o in critical)
    words = {p[j:j + 8] for p, _ in leaves for j in range(len(p) - 7)}
    absent = sorted({format(i, '08b') for i in range(256)} - words)
    assert absent == ['00000000', '00000001']
    records, spare = rm_witness(leaves)
    last = records[-1]
    reachable = frame(last['pc'], last['gap'], last['registers'], spare)
    boot = run_to(rows, (0, 0, set()), reachable, 3000000)
    assert boot['status'] == 'reached'
    expected_pc, overflow = increment(strip('0', 1, last['path']))
    assert not overflow and expected_pc == '11101001001000001'
    expected = frame(expected_pc, last['gap'], last['registers'], spare)
    original = run_to(rows, reachable, expected, 10000)
    assert original['status'] == 'reached'
    # Old58/0 -> old84, deleting old74. Compact labels are 30, 32, 31.
    assert rows[30, 0] == (0, -1, 31)
    changed = rows.copy()
    changed[30, 0] = (0, -1, 32)
    del changed[31, 0], changed[31, 1]
    assert len(changed) == 504
    assert all(q != 31 for w, d, q in changed.values())
    wrong_pc = '11101001001001'
    wrong = frame(wrong_pc, last['gap'], last['registers'], spare)
    modified = run_to(changed, reachable, wrong, 10000)
    assert modified['status'] == 'reached'
    assert wrong[2] != expected[2]
    # The wrong frame is not merely a later frame after a correct completion:
    # the edited run never visits the expected frame during this continuation.
    no_earlier_correct = run_to(changed, reachable, expected, modified['steps'])
    assert no_earlier_correct['status'] == 'limit'
    result = dict(
        source_commit=PIN, machine_sha256=TABLE_SHA, program_sha256=PROG_SHA,
        model='bi-infinite binary blank tape; start0; halt253 not counted',
        original_states=253, rejected_scanner_states=252,
        program_nodes=6459, instruction_leaves=6460,
        maximum_depth=max(map(lambda item: len(item[0]), leaves)),
        zero_run_distribution=dict(sorted(zero_runs.items())),
        absent_length8_words=absent, critical_leaves=critical,
        rm_records=records, literal_blank_reachability=boot,
        complete_reachable_frame=dict(state=reachable[0], head=reachable[1],
                                      ones=sorted(reachable[2]), spare_blocks=len(spare)),
        expected_pc=expected_pc, original_macro=original,
        wrong_pc=wrong_pc, shortened_scanner_wrong_macro=modified,
        expected_frame_absent_through_wrong_frame=True,
        limitation='The 252-state scanner edit is rejected; this is a finite source-control '
                   'counterexample, not a proof of different ultimate blank-tape halting. '
                   'No new valid consistency machine or kernel theorem is claimed.')
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items()
                      if k not in ('critical_leaves', 'complete_reachable_frame')}, indent=2))


if __name__ == '__main__':
    main()
