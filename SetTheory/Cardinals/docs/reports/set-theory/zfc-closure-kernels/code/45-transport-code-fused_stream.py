#!/usr/bin/env python3
"""Two explicit streaming maps on free names; not a binary Turing machine.

The lexical representation and s/S implementations follow ProveIt source 28,
whose unmodified four-map comparator is retained in vendor/stream_four.py.
The primitive u increments. The primitive w maps 0->1, 1->-1 and
otherwise decrements. Modes v, S and g are retained only as intermediate
comparators, not as primitives of the two-map kernel. Bound indices are
copied exactly. A separate proof kernel checks syntax and binding.

These are deterministic binary-input, variable-output transducers. An edge
can emit multiple bits. Counts here must not be reported as TM state counts.
"""
from __future__ import annotations

from collections import deque

PRIMITIVES = ('u', 'w')
MODES = ('u', 'w', 'v', 's', 'S', 'g')
INIT = ('tag',)


def scalar(mode: str, value: int) -> int:
    if mode in ('s', 'u'):
        return value + 1
    if mode == 'S':
        return value - 1
    if mode == 'g':
        return 1 if value == 0 else 0 if value in (1, 2) else value
    if mode == 'v':
        return 0 if value == 0 else -1 if value in (1, 2) else value - 1
    if mode == 'w':
        return 1 if value == 0 else -1 if value == 1 else value - 1
    raise ValueError('unknown mode')


def finish_field(slot):
    return ('var', 2) if slot == 1 else INIT


def transition(mode, state, bit):
    if mode not in MODES or bit not in ('0', '1'):
        raise ValueError('unknown mode or input bit')
    if mode == 'u':
        mode = 's'
    phase = state[0]
    if phase == 'tag':
        return ('tag2', bit), bit
    if phase == 'tag2':
        return (('var', 1) if state[1] == bit == '1' else INIT), bit
    slot = state[1]
    done = finish_field(slot)
    if phase == 'var':
        return (('copy', slot) if bit == '0' else ('sign', slot)), bit
    if phase == 'copy':
        return (('copy', slot) if bit == '1' else done), bit
    if phase == 'sign':
        if (mode == 's' and bit == '0') or (mode in ('S', 'v', 'w') and bit == '1'):
            return ('copy', slot), bit + '1'
        if mode == 'g' and bit == '1':
            return ('copy', slot), '1'
        return ('pending', slot), ''
    if phase == 'pending':
        if mode == 's':
            return (done, '00') if bit == '0' else (('copy', slot), '1')
        if mode == 'S':
            return (done, '10') if bit == '0' else (('copy', slot), '0')
        return (done, '010' if mode in ('g', 'w') else '00') if bit == '0' else (('second', slot), '')
    if phase == 'second' and mode == 'w':
        return (done, '10') if bit == '0' else (('copy', slot), '01')
    if phase == 'second' and mode in ('g', 'v'):
        return (done, '00' if mode == 'g' else '10') if bit == '0' else (('third', slot), '')
    if phase == 'third' and mode in ('g', 'v'):
        return (done, '00' if mode == 'g' else '10') if bit == '0' else (('copy', slot), '0111' if mode == 'g' else '011')
    raise ValueError('unreachable scanner state')


def transduce(mode, bits):
    state, output = INIT, []
    for bit in bits:
        state, word = transition(mode, state, bit)
        output.append(word)
    if state != INIT:
        raise ValueError('incomplete lexical token')
    return ''.join(output)


def table(mode):
    labels, queue = {INIT: 0}, deque([INIT])
    rows = []
    while queue:
        state = queue.popleft()
        for bit in '01':
            target, word = transition(mode, state, bit)
            if target not in labels:
                labels[target] = len(labels)
                queue.append(target)
            rows.append([labels[state], int(bit), word, labels[target]])
    return {'mode': mode, 'states': len(labels), 'initial': 0,
            'accepting': [0], 'labels': [list(x) for x in labels],
            'rows': rows,
            'model': 'deterministic binary-input variable-output stream transducer'}


def apply_word(word, bits):
    for mode in word:
        bits = transduce(mode, bits)
    return bits
