#!/usr/bin/env python3
"""Explicit indexed finite three-counter compiler for the K215 TM0 adapter.

An independent stdlib-only transcription of the definitions in the pinned
CounterMacros100.lean and TuringCounter100.lean. No repository code is imported
or executed. The numerical symbol and state orders are fixed, not chosen.
"""
from collections import Counter
from hashlib import sha256
from itertools import product
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parent
ADAPTER = json.loads((ROOT / 'k215_tm0_240.json').read_text())
TM = {(r['state'], r['read']): r['action'] for r in ADAPTER['transition_rows']}
NQ, BASE, STRIDE, PUSH_OFFSET = 240, 4, 26, 12
NBLOCKS = 4 + NQ + NQ * BASE + NQ * BASE * BASE
LENGTH = STRIDE * NBLOCKS

def sym(digit):
    return int(digit == 2)

def code(symbol):
    return symbol + 1

def incs(r, d, location, exit, offset):
    return ('inc', r, location + offset + 1 if offset + 1 < d else exit)

def transfer(r, s, location, exit, offset):
    return ('test', r, exit, location + 1) if offset == 0 else ('inc', s, location)

def mul_transfer(r, s, k, location, exit, offset):
    if offset == 0:
        return ('test', r, exit, location + 1)
    return incs(s, k, location + 1, location, offset - 1)

def push(r, scratch, k, digit, location, exit, offset):
    if offset < k + 1:
        return mul_transfer(r, scratch, k, location, location + k + 1, offset)
    if offset < k + 3:
        return transfer(scratch, r, location + k + 1, location + k + 3, offset - k - 1)
    return incs(r, digit, location + k + 3, exit, offset - k - 3)

def pop(r, scratch, k, location, exits, offset):
    if offset < k:
        return ('test', r, location + k + 1 + 2 * offset,
                location + offset + 1 if offset + 1 < k else location + k)
    if offset == k:
        return ('inc', scratch, location)
    remainder, local = divmod(offset - k - 1, 2)
    return transfer(scratch, r, location + k + 1 + 2 * remainder,
                    exits(remainder), local)

def dispatch_id(state, digit):
    return 4 + NQ + BASE * state + digit

def left_id(state, digit, left_digit):
    return 4 + NQ + NQ * BASE + (BASE * state + digit) * BASE + left_digit

def dispatch(state, digit, location, offset):
    action = TM[state, sym(digit)]
    if action is None:
        return ('test', 2, 3 * STRIDE, 3 * STRIDE)
    target, kind, value = action
    exit = STRIDE * (4 + target)
    if kind == 'write':
        return push(1, 2, BASE, code(value), location, exit, offset)
    if value == 'R':
        return push(0, 2, BASE, code(sym(digit)), location, exit, offset)
    return pop(0, 2, BASE, location,
               lambda j: STRIDE * left_id(state, digit, j), offset)

def left_code(state, digit, left_digit, location, offset):
    action = TM[state, sym(digit)]
    if action is None or action[1:] != ['move', 'L']:
        return ('stop',)
    target = action[0]
    if offset < PUSH_OFFSET:
        return push(1, 2, BASE, code(sym(digit)), location,
                    location + PUSH_OFFSET, offset)
    return push(1, 2, BASE, code(sym(left_digit)), location + PUSH_OFFSET,
                STRIDE * (4 + target), offset - PUSH_OFFSET)

def block(block_id, offset):
    location = STRIDE * block_id
    if block_id == 0:
        if offset == 0:
            return ('test', 0, STRIDE * 4, 1)
        if offset == 1:
            return ('inc', 0, 2)
        return pop(0, 2, 2, 2, lambda j: STRIDE * (1 + j), offset - 2)
    if block_id < 3:
        # enc maps both binary digits to blank, whose positive code is one.
        return push(1, 2, BASE, 1, location, 0, offset)
    if block_id == 3:
        if offset < 3:
            return ('test', offset, location + offset + 1, location + offset)
        return ('accept',)
    if block_id < 4 + NQ:
        return pop(1, 2, BASE, location,
                   lambda j: STRIDE * dispatch_id(block_id - 4, j), offset)
    if block_id < 4 + NQ + NQ * BASE:
        state, digit = divmod(block_id - 4 - NQ, BASE)
        return dispatch(state, digit, location, offset)
    if block_id < NBLOCKS:
        pair, left_digit = divmod(block_id - 4 - NQ - NQ * BASE, BASE)
        state, digit = divmod(pair, BASE)
        return left_code(state, digit, left_digit, location, offset)
    return ('stop',)

def instruction(address):
    return block(*divmod(address, STRIDE))

def step(code_fn, address, registers):
    row = code_fn(address)
    values = list(registers)
    if row[0] == 'inc':
        values[row[1]] += 1
        return row[2], tuple(values)
    if row[0] == 'test':
        if values[row[1]] == 0:
            return row[2], tuple(values)
        values[row[1]] -= 1
        return row[3], tuple(values)
    return None

def run_to(code_fn, start, registers, exits, bound=1000000):
    address, values = start, tuple(registers)
    for count in range(bound):
        if count and address in exits:
            return address, values, count
        result = step(code_fn, address, values)
        assert result is not None, (address, values, code_fn(address))
        address, values = result
    raise AssertionError(('bounded audit exceeded', start, registers, address, values))

def decode_stack(number):
    output = []
    while number:
        number, digit = divmod(number, BASE)
        assert digit in (1, 2)
        output.append(sym(digit))
    return output

def strip_blanks(values):
    values = list(values)
    while values and values[-1] == 0:
        values.pop()
    return values

def good_numbers(max_length=2):
    values = [0]
    for length in range(1, max_length + 1):
        values.extend(sum(d * BASE ** i for i, d in enumerate(digits))
                      for digits in product((1, 2), repeat=length))
    return values

def main():
    rows = [instruction(address) for address in range(LENGTH)]
    kind_counts = Counter(row[0] for row in rows)
    edges = 0
    out_of_range_padding = []
    for address, row in enumerate(rows):
        if row[0] in ('inc', 'test'):
            assert row[1] in range(3)
            for target in row[2:]:
                assert target >= 0, row
                if target < LENGTH:
                    edges += 1
                else:
                    block_id, offset = divmod(address, STRIDE)
                    assert 4 + NQ <= block_id < 4 + NQ + NQ * BASE
                    state, digit = divmod(block_id - 4 - NQ, BASE)
                    assert TM[state, sym(digit)][1:] == ['move', 'L']
                    assert offset >= 3 * BASE + 1
                    out_of_range_padding.append(dict(address=address, target=target))
    macro_cases = 0
    for r, k, digit, number in product((0, 1), (2, 4), (1, 2), range(32)):
        if digit >= k:
            continue
        registers = [7, 7, 0]
        registers[r] = number
        finish, result, _ = run_to(lambda o: push(r, 2, k, digit, 0, 1000, o),
                                   0, registers, {1000})
        expected = list(registers)
        expected[r] = k * number + digit
        assert result == tuple(expected)
        macro_cases += 1
    for r, k, number in product((0, 1), (2, 4), range(64)):
        registers = [7, 7, 0]
        registers[r] = number
        finish, result, _ = run_to(lambda o: pop(r, 2, k, 0, lambda j: 1000 + j, o),
                                   0, registers, set(range(1000, 1000 + k)))
        expected = list(registers)
        expected[r] = number // k
        assert finish == 1000 + number % k and result == tuple(expected)
        macro_cases += 1
    loader_cases = []
    for x in (0, 1, 2, 3, 4, 7, 15, 255):
        finish, result, count = run_to(instruction, 0, (x, 0, 0), {STRIDE * 4})
        expected = (4 ** x.bit_length() - 1) // 3
        assert result == (0, expected, 0)
        loader_cases.append(dict(input=x, counter_steps=count, output_B=expected))
    # Cover every state with small good stack halves. Compare the decoded tape
    # after one complete TM0 instruction, modulo trailing blank symbols.
    simulation_cases, halt_cases = 0, 0
    loops = {STRIDE * (4 + q) for q in range(NQ)}
    for q, a, b in product(range(NQ), good_numbers(), good_numbers()):
        left, right = decode_stack(a), decode_stack(b)
        scanned = right[0] if right else 0
        tail = right[1:] if right else []
        action = TM[q, scanned]
        dispatch_address, dispatch_values, _ = run_to(
            instruction, STRIDE * (4 + q), (a, b, 0),
            {STRIDE * dispatch_id(q, j) for j in range(BASE)})
        address, result, _ = run_to(instruction, dispatch_address, dispatch_values,
                                    loops | {3 * STRIDE + 3})
        if action is None:
            assert address == 3 * STRIDE + 3 and result == (0, 0, 0)
            halt_cases += 1
        else:
            target, kind, value = action
            assert address == STRIDE * (4 + target) and result[2] == 0
            if kind == 'write':
                expected_left, expected_right = left, [value] + tail
            elif value == 'R':
                expected_left, expected_right = [scanned] + left, tail
            else:
                new_head = left[0] if left else 0
                expected_left = left[1:] if left else []
                expected_right = [new_head, scanned] + tail
            assert strip_blanks(decode_stack(result[0])) == strip_blanks(expected_left)
            assert strip_blanks(decode_stack(result[1])) == strip_blanks(expected_right)
        simulation_cases += 1
    output = ROOT / 'k215_counter_program.json'
    output.write_text(json.dumps(dict(
        format='CInstr: [inc,register,target], [test,register,zero_target,positive_decrement_target], [accept], or [stop]',
        register_count=3, initial_address=0, initial_registers=[1, 0, 0],
        length=LENGTH, code=rows), separators=(',', ':')) + '\n')
    report = dict(
        status='PASS_INDEXED_THREE_COUNTER_COMPILER', symbol_count=2, state_count=NQ,
        base=BASE, stride=STRIDE, left_push_offset=PUSH_OFFSET,
        block_count=NBLOCKS, program_length=LENGTH,
        instruction_kind_counts=dict(kind_counts), in_range_targets=edges,
        out_of_range_targets_in_unreachable_pop_padding=out_of_range_padding,
        push_pop_macro_cases=macro_cases, loader_cases=loader_cases,
        exhaustive_small_stack_TM0_cases=simulation_cases, halt_cases=halt_cases,
        program_json_sha256=sha256(output.read_bytes()).hexdigest(),
        caveat='Fresh finite audits of an explicit reimplementation; not a new proof-assistant build or a decision of eventual K215 halting.')
    (ROOT / 'k215_counter_compiler_audit.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))

if __name__ == '__main__':
    main()
