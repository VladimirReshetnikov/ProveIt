"""Compact blank initializer from closure-kernel source 21, batch 150.

Adapted from zfc_epsc2_proposal.zip at arrival47e887108, by OpenAI for
Vladimir Reshetnikov (2026-10-16). The delivered implementation and ordinary
proof remain preserved in the closure-kernel host. This reusable component
constructs a complete counted initializer, not a new consistency machine.
The Mira-Cult/Jeff runtime is separately attributed in mira_backend.py.
"""
from __future__ import annotations

import hashlib
import json

PHYSICAL_ORDER = (2, 4, 3, 7, 6, 8, 0, 1, 5)


def choose_parameters(minimum_gap):
    """Minimize our explicit state formula; break ties by time then gap."""
    if type(minimum_gap) is not int or minimum_gap < 1:
        raise ValueError('minimum_gap must be positive')
    candidates = []
    for n in range(1, max(2, minimum_gap + 1)):
        m = max(1, (max(0, minimum_gap-2)+n-1)//n-2)
        gap = n*(m+2)+2
        candidates.append((28+2*n+m, 28+6*n+(m+2)*n*(n+2), gap, n, m))
    _, _, _, n, m = min(candidates)
    return n, m


def make_initializer(initial, n, m, target='return'):
    """Return a total labeled binary transition table and exact contract.

    Tape initially blank, state i:0, head 0. On exit target, tape has a
    marker, gap zeros, a header, and exactly nine encoded unary registers.
    The head is immediately right of the marker. No scratch marks remain.
    """
    initial = tuple(initial)
    if len(initial) != 9 or any(type(x) is not int or x < 0 for x in initial):
        raise ValueError('exactly nine natural initial registers required')
    if type(n) is not int or type(m) is not int or n < 1 or m < 1:
        raise ValueError('positive counter count and stride required')
    if target.startswith('i:'):
        raise ValueError('exit label must not collide with initializer labels')
    registers = [b for j in PHYSICAL_ORDER for b in [0]+[1]*(initial[j]+1)]
    wire = list(reversed(registers)) + [1,1] + [0,1]*n + [0,1]
    table = {}

    def put(q, b, w, direction, dest):
        if (q,b) in table: raise ValueError('duplicate row')
        table[q,b] = w,direction,dest

    for j, w in enumerate(wire):
        last = j+1 == len(wire)
        for b in (0,1):
            put(f'i:{j}', b, w, 'R' if last else 'L',
                'i:right' if last else f'i:{j+1}')
    # The first remaining isolated 1 is a counter; adjacent 11 is the end.
    put('i:right',0,0,'R','i:right')
    put('i:right',1,1,'R','i:test')
    put('i:test',0,0,'L','i:consume')
    put('i:test',1,1,'L','i:finish_erase')
    for b in (0,1): put('i:consume',b,0,'L','i:left')
    put('i:left',0,0,'L','i:left')
    put('i:left',1,0,'L','i:stride0')
    for j in range(m):
        last = j+1 == m
        for b in (0,1):
            put(f'i:stride{j}',b,1 if last else 0,'R' if last else 'L',
                'i:right' if last else f'i:stride{j+1}')
    for b in (0,1): put('i:finish_erase',b,0,'L','i:finish_left')
    put('i:finish_left',0,0,'L','i:finish_left')
    put('i:finish_left',1,1,'R',target)
    S = sum(initial)
    contract = dict(counter_count=n, stride=m, gap=n*(m+2)+2,
                    initializer_states=S+28+2*n+m,
                    blank_steps=S+28+6*n+(m+2)*n*(n+2),
                    initial_registers=list(initial), physical_order=list(PHYSICAL_ORDER),
                    scratch_marks_on_exit=0, spare_register_blocks=0)
    assert len(table) == 2*contract['initializer_states']
    assert all(direction in ('L','R') and w in (0,1)
               for w,direction,dest in table.values())
    return table, contract


def simulate_initializer(table, contract, target='return'):
    """Independent literal transition replay and exact whole-tape check."""
    q, head, tape = 'i:0', 0, set()
    for steps in range(contract['blank_steps'] + 1):
        if q == target: break
        w, direction, q = table[q,int(head in tape)]
        if w: tape.add(head)
        else: tape.discard(head)
        head += 1 if direction == 'R' else -1
    else: raise AssertionError('initializer exceeded proved step count')
    initial = contract['initial_registers']
    bits = [1]+[0]*contract['gap']+[1]
    bits += [b for j in PHYSICAL_ORDER for b in [0]+[1]*(initial[j]+1)]
    expected = {head-1+i for i,b in enumerate(bits) if b}
    assert q == target and steps == contract['blank_steps']
    assert tape == expected
    assert head == -(18+sum(initial)+contract['gap'])
    # Serialize the entire finite support, not a finite window of the tape.
    digest = hashlib.sha256(json.dumps(dict(head=head,ones=sorted(tape)),
                           sort_keys=True,separators=(',',':')).encode()).hexdigest()
    return dict(passed=True,steps=steps,head=head,ones=len(tape),
                configuration_sha256=digest)

