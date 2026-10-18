#!/usr/bin/env python3
"""Independent finite replay of the rejected 178 rotation with its failed repair.

The table is a diagnostic counterexample, not a claimed ZFC-consistency machine.
This script checks a blank prefix and records a bounded instruction rejection.
"""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parents[1]


def paint(pc, head, header, registers):
    ones = {head - 1, header}
    ones.update(head + i for i, b in enumerate(pc) if b == '1')
    pos = header + 1
    for value in registers:
        ones.update(range(pos + 1, pos + value + 2))
        pos += value + 2
    return ones


def increment(word):
    bits = list(word)
    for i in range(len(bits) - 1, -1, -1):
        if bits[i] == '0':
            bits[i] = '1'
            return ''.join(bits)
        bits[i] = '0'
    raise AssertionError('Unexpected path overflow in fixed example')


def step(table, state, head, ones):
    write, direction, state = table[state, int(head in ones)]
    if write:
        ones.add(head)
    else:
        ones.discard(head)
    return state, head + direction


def main():
    raw = (ROOT / 'results/rotation178_245_old.tm').read_bytes()
    table = {}
    for line in raw.decode().splitlines():
        q, b, w, d, t = line.split()
        table[int(q), int(b)] = int(w), 1 if d == 'R' else -1, int(t)
    assert len(table) == 490 and all(q != 208 for q, b in table)
    table[218, 0] = (0, -1, 178)
    state, head, ones = 95, 0, set()
    for tick in range(410735):
        assert state != 254
        state, head = step(table, state, head, ones)
    registers = [0, 0, 0, 3, 0, 0, 3, 0, 0]
    target = paint('', -5, 176, registers + [1] * 167)
    assert (state, head) == (96, -5) and ones == target and len(ones) == 351
    bootstrap = dict(status='EXACT_FINITE_REPLAY_PASS', steps=410735,
                     state=state, head=head, marker=-6, header=176,
                     physical_registers=registers, spare_count=167,
                     spare_value=1, one_count=351,
                     all_one_positions=sorted(ones), all_other_cells_zero=True)
    pc = '11101001001010100010110000'
    registers = [0, 3, 6, 2, 5, 1, 4, 0, 3]
    assert registers[0] == 0 and pc.endswith('0')
    expected_pc = increment(pc[:-1])
    target = paint(expected_pc, 0, 40, registers + [0])
    state, head, ones = 96, 0, paint(pc, 0, 40, registers + [0])
    visits = 0
    for tick in range(100000):
        assert state != 254
        state, head = step(table, state, head, ones)
        if state == 96:
            assert (head, ones) != (0, target), 'Unexpected pass of rejected case'
            visits += 1
            if visits == 16:
                break
    else:
        raise AssertionError('Expected recorded 16-dispatch rejection')
    rejection = dict(status='BOUNDED_LITERAL_INSTRUCTION_REJECTED', steps=tick+1,
                     dispatcher_visits=visits, pc=pc, logical_operation='CD2/zero',
                     head_at_entry=0, header_at_entry=40,
                     physical_registers=registers, spares=[0],
                     expected_pc=expected_pc, actual_head=head,
                     wrong_ones=sorted(ones-target), missing_ones=sorted(target-ones))
    out = dict(status='REJECTED_PROPOSAL_ONLY', baseline_rotated_table_sha256=
               hashlib.sha256(raw).hexdigest(), additional_edit='218/0=0 L 178',
               blank_replay=bootstrap, instruction_rejection=rejection,
               scope='Finite evidence and bounded rejection; no assertion about blank-tape halting or a valid 245-state replacement.')
    (ROOT / 'results/rotation178_repair_replay.json').write_text(
        json.dumps(out, indent=2) + '\n')
    print(json.dumps({k: v for k, v in out.items() if k != 'blank_replay'}, indent=2))


if __name__ == '__main__':
    main()
