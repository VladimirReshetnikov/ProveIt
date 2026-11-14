#!/usr/bin/env python3
"""A concrete decoder-prefix mismatch, not a blank-halting inequivalence."""
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent

def table():
    result = {}
    for line in (HERE / 'pa196.native.tm').read_text().splitlines():
        if not line or line.startswith('#'):
            continue
        q, bit, w, d, target = line.split()
        result[int(q), int(bit)] = (int(w), 1 if d == 'R' else -1, int(target))
    return result

def edge(t, prefix, limit=100):
    tape = {-1: 1, **{i: int(b) for i, b in enumerate(prefix+'0')}}
    original = dict(tape)
    head, state = len(prefix), 69
    for step in range(limit):
        if step and head == len(prefix)+1:
            return state if tape == original else None
        if head not in tape or (state, tape[head]) not in t:
            return None
        write, direction, state = t[state, tape[head]]
        tape[head] = write
        head += direction
    return None

def main():
    old = table()
    if edge(old, '01') != 105:
        raise ValueError('Original node20 entry does not match its expected child')
    new = dict(old)
    new.update({(84,0):(0,1,68), (84,1):(1,1,53),
                (53,0):(0,1,310), (53,1):(1,1,62),
                (310,0):(0,1,69), (310,1):(1,1,214)})
    actual = edge(new, '100')
    if actual != 104 or actual == 105:
        raise ValueError('Expected concrete wrong-child witness changed')
    patches = []
    states = sorted({q for q, bit in new})
    targets = sorted(set(states) | {target for _, _, target in new.values()})
    for write in (0,1):
        for direction in (-1,1):
            for target in targets:
                new[69,0] = (write,direction,target)
                if edge(new,'100') == 105 and edge(new,'1011010011000') == 104:
                    patches.append((write,direction,target))
    if patches:
        raise ValueError(('Unexpected one-row repair',patches))
    print(json.dumps({'status':'DECODER_PREFIX_COUNTEREXAMPLE_CONFIRMED',
                      'old_prefix':'01','new_prefix':'100',
                      'expected_child':105,'actual_child':actual,
                      'single_row_actions_tested':4*len(targets),
                      'working_targets':len(states),
                      'halt_targets':len(set(targets)-set(states)),
                      'single_row_repairs':0,
                      'scope':'Preserved-prefix child-selection specification only; no claimed blank-halting counterexample.'},indent=2))

if __name__ == '__main__':
    main()
