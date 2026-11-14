#!/usr/bin/env python3
"""Reproduce the rejected six-zero shortcut; never assert it is a candidate."""
from check_window import read_table, need

def run_to_dispatch(table, config):
    state, head, frozen = config
    tape = set(frozen)
    trace = []
    for step in range(10000):
        read = int(head in tape)
        write, direction, target = table[state, read]
        trace.append([state, head, read, write, direction, target])
        if write:
            tape.add(head)
        else:
            tape.discard(head)
        head += direction
        state = target
        if state in (84, 254):
            return (state, head, frozenset(tape)), trace
    raise ValueError('No dispatcher return within the concrete check bound')

def check(root):
    old = read_table(root / 'data/u208.native.tm')
    need(old[23, 0] == (0, -1, 34), 'Unexpected baseline predecessor')
    new = {key: value for key, value in old.items() if key[0] != 34}
    new[23, 0] = (0, -1, 75)
    need(len(new) == 414, 'Rejected table census')
    # CD8 at PC000000, nine zero registers, one zero spare, zero gap.
    initial = (84, 0, frozenset({-1, 56, *range(58, 77, 2)}))
    old_first, old_prefix = run_to_dispatch(old, initial)
    new_first, new_prefix = run_to_dispatch(new, initial)
    need(old_first == new_first, 'First internal return changed unexpectedly')
    old_second, old_trace = run_to_dispatch(old, old_first)
    new_second, new_trace = run_to_dispatch(new, new_first)
    need(old_second[0:2] == (84, 0), 'Old second endpoint')
    need(new_second[0:2] == (84, 8), 'Rejected second endpoint')
    need(old_second[2] == new_second[2], 'Expected same tape')
    expected = {-1, *range(7, 57), 58, 62, 64, 66, 68, 70, 72, 74, 76}
    need(old_second[2] == frozenset(expected), 'Complete endpoint tape')
    return {
        'status': 'REJECTED_207_SHORTCUT_REPRODUCED',
        'old_working_states': 208, 'rejected_working_states': 207,
        'source_site': ['000000', 'CD', 8],
        'old_first_steps': len(old_prefix), 'new_first_steps': len(new_prefix),
        'old_second_segment_steps': len(old_trace),
        'new_second_segment_steps': len(new_trace),
        'old_second_head': old_second[1], 'new_second_head': new_second[1],
        'same_complete_tape': True, 'endpoint_ones': sorted(expected),
        'old_second_trace': old_trace, 'new_second_trace': new_trace,
    }
