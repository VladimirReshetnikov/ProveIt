"""Literal binary blank initializers with a binary odometer.

Independent construction, OpenAI for Vladimir Reshetnikov, 2026-10-17.
The output frame follows the attributed Mira-Cult/Jeff/Wade register engine.
This file constructs and checks initializers; it makes no new Con(ZFC) claim.
"""
from __future__ import annotations

import hashlib
import json

PHYSICAL_ORDER = (2, 4, 3, 7, 6, 8, 0, 1, 5)


def _rows(kind, initial, n, target):
    if kind not in ('auxiliary', 'registers'):
        raise ValueError('unknown initializer kind')
    if type(n) is not int or n < 1:
        raise ValueError('positive bit count required')
    initial = tuple(initial)
    if len(initial) != 9 or any(type(x) is not int or x < 0 for x in initial):
        raise ValueError('nine natural register values required')
    if kind == 'registers' and (n < 9 or initial[0] not in (0, 2) or any(initial[1:])):
        raise ValueError('register odometer needs n >= 9 and only nextproof = 0 or 2')
    if target.startswith('o:'):
        raise ValueError('target collides with private initializer names')
    table = {}

    def put(q, b, w, d, t):
        key = 'o:' + q, b
        if key in table:
            raise ValueError('duplicate row')
        table[key] = w, d, t if t == target else 'o:' + t

    # At dec_sep the head is on the separator immediately before the low bit.
    put('dec_sep', 0, 0, 'R', 'dec_bit')
    put('dec_bit', 0, 1, 'R', 'dec_sep')
    put('dec_bit', 1, 0, 'L', 'back_scan')
    put('back_scan', 0, 0, 'L', 'back_scan')
    put('back_scan', 1, 1, 'L', 'back_test')
    put('back_test', 0, 0, 'L', 'back_scan')
    put('back_test', 1, 1, 'L', 'find_marker')
    put('find_marker', 0, 0, 'L', 'find_marker')
    put('find_marker', 1, 0, 'L', 'place_marker')
    put('place_marker', 0, 1, 'R', 'seek_sentinel')
    put('place_marker', 1, 1, 'R', 'seek_sentinel')
    put('seek_sentinel', 0, 0, 'R', 'seek_sentinel')
    put('seek_sentinel', 1, 1, 'R', 'skip_sentinel')
    put('skip_sentinel', 1, 1, 'R', 'dec_sep')
    put('exit_scan', 0, 0, 'L', 'exit_scan')
    put('exit_scan', 1, 1, 'R', target)
    regs = [b for r in PHYSICAL_ORDER for b in [0] + [1]*(initial[r]+1)]
    if kind == 'auxiliary':
        put('dec_sep', 1, 0, 'L', 'clean_bit')
        put('clean_bit', 1, 0, 'L', 'clean_sep')
        put('clean_sep', 0, 0, 'L', 'clean_bit')
        put('clean_sep', 1, 0, 'L', 'exit_scan')
        wire = list(reversed(regs)) + [1, 1] + [1, 0]*n + [1, 1, 0, 1]
        free_zero = ['skip_sentinel', 'clean_bit']
        expected_states = sum(initial) + 32 + 2*n
        gap = (1 << n) + 2*n + 3
        blank_steps = sum(initial) + 17 + 2*n + (1 << (2*n)) + 14*(1 << n)
        spare = []
    else:
        put('dec_sep', 1, 0, 'L' if initial[0] else 'R',
            'seed2' if initial[0] else 'erase_right')
        put('erase_right', 1, 0, 'L', 'finish_scan')
        put('finish_scan', 0, 0, 'L', 'finish_scan')
        put('finish_scan', 1, 1, 'L', 'finish_test')
        put('finish_test', 0, 0, 'L', 'finish_scan')
        put('finish_test', 1, 0, 'L', 'exit_scan')
        wire = [1, 1] + [1, 0]*n + [1, 1, 0, 1]
        free_zero = ['skip_sentinel', 'erase_right']
        expected_states = 2*n + 15
        gap = (1 << n) + 1
        blank_steps = 2*n + 1 + (1 << (2*n)) + 14*(1 << n) - initial[0]
        spare = [0]*(n-9)

    # On a monotone blank-tape print the current cell is always zero. The
    # indicated states read only one in the subsequent odometer phase.
    # Their read-zero rows therefore implement the first two output cells.
    emitters = free_zero + [f'seed{k}' for k in range(2, len(wire)-1)]
    emitters += ['place_marker']
    assert len(emitters) == len(wire) and wire[-1] == 1
    for k, (q, w) in enumerate(zip(emitters[:-1], wire[:-1])):
        put(q, 0, w, 'L', emitters[k+1])
        if q not in free_zero:
            put(q, 1, w, 'L', emitters[k+1])
    borrowed_one = []
    if kind == 'registers' and initial[0] == 2:
        # On underflow every counter bit is one. Keep the rightmost sentinel
        # one as the final register bit; the first sentinel is now zero.
        # Flip the separator of physical block 7 to one. Blocks 6 and 7 then
        # become 0111, encoding value two in physical block 6 (nextproof).
        # All later blocks shift one position in the list and remain zero.
        # The initial monotone writer reads only zero; these seed/read-one
        # rows are therefore available for this fixed length return walk.
        k = n-7
        for j in range(k):
            q = f'o:seed{2+2*j}'
            t = f'o:seed{3+2*j}' if j+1 < k else f'o:seed{2*k+2}'
            table[q, 1] = 1, 'L', t
            borrowed_one.append(q)
        q = f'o:seed{2*k+3}'
        table[q, 1] = 1, 'L', 'o:finish_scan'
        borrowed_one.append(q)
    states = {q for q, b in table}
    assert len(states) == expected_states
    assert set(table) == {(q, b) for q in states for b in (0, 1)}
    assert all(w in (0, 1) and d in ('L', 'R') and (t in states or t == target)
               for w, d, t in table.values())
    contract = dict(kind=kind, counter_bits=n, initial_registers=list(initial),
                    physical_order=list(PHYSICAL_ORDER), spare_registers=spare,
                    initializer_states=expected_states, gap=gap,
                    blank_steps=blank_steps, seed_steps=len(wire),
                    successful_decrements=(1 << n)-1,
                    reused_read_zero_states=['o:'+q for q in free_zero],
                    reused_read_one_seed_states=borrowed_one,
                    start='o:'+emitters[0], target=target,
                    ordinary_proof=True, kernel_checked=False)
    return table, contract


def make_auxiliary(initial=(0,)*9, n=7, target='return'):
    return _rows('auxiliary', initial, n, target)


def make_register_clock(n=9, target='return', nextproof=0):
    return _rows('registers', (nextproof,)+(0,)*8, n, target)


def make_zero_single_sentinel(n=9, target='return'):
    """Zero-register variant with one end-sentinel cell rather than two.

    The decrement's separator phase detects a one without a second sentinel
    cell. Cleanup can return left immediately after erasing that one.
    """
    table, contract = make_register_clock(n, target)
    assert table['o:seed2', 0] == table['o:seed2', 1] == (1, 'L', 'o:seed3')
    # Start at the old second writer. The old first writer's runtime state
    # is still needed, and its now-free read-zero row absorbs seed2.
    table['o:skip_sentinel', 0] = table['o:seed2', 0]
    table = {(q, b): (w, d, 'o:skip_sentinel' if t == 'o:seed2' else t)
             for (q, b), (w, d, t) in table.items() if q != 'o:seed2'}
    table['o:dec_sep', 1] = 0, 'L', 'o:finish_scan'
    contract = dict(contract, kind='registers_one_sentinel', start='o:erase_right',
                    initializer_states=2*n+14, seed_steps=2*n+5,
                    blank_steps=(1 << (2*n))+14*(1 << n)+2*n-2)
    assert len(table) == 2*contract['initializer_states']
    return table, contract


def simulate(table, contract):
    """Literal one-cell replay; compares the entire finite support."""
    q, h, tape = contract['start'], 0, set()
    for steps in range(contract['blank_steps']+1):
        if q == contract['target']:
            break
        w, d, q = table[q, int(h in tape)]
        if w:
            tape.add(h)
        else:
            tape.discard(h)
        h += 1 if d == 'R' else -1
    else:
        raise AssertionError('declared exit was not reached')
    assert steps == contract['blank_steps'], (steps, contract['blank_steps'])
    initial = contract['initial_registers']
    vals = [initial[r] for r in PHYSICAL_ORDER] + contract['spare_registers']
    bits = [1] + [0]*contract['gap'] + [1]
    bits += [b for v in vals for b in [0]+[1]*(v+1)]
    expected = {h-1+k for k, b in enumerate(bits) if b}
    assert tape == expected, dict(extra=sorted(tape-expected), missing=sorted(expected-tape))
    encoded = json.dumps(dict(head=h, ones=sorted(tape)), sort_keys=True,
                         separators=(',', ':')).encode()
    return dict(passed=True, steps=steps, head=h, one_cells=len(tape),
                whole_tape_sha256=hashlib.sha256(encoded).hexdigest(),
                final_ones=sorted(tape))


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('assertions must be enabled')
    cases = []
    for n in range(1, 10):
        for initial in [(0,)*9, (2,)+(0,)*8, tuple(range(9))]:
            table, contract = make_auxiliary(initial, n)
            cases.append(dict(contract=contract, simulation=simulate(table, contract)))
    for n in range(9, 12):
        for np in (0, 2):
            table, contract = make_register_clock(n, nextproof=np)
            cases.append(dict(contract=contract, simulation=simulate(table, contract)))
        table, contract = make_zero_single_sentinel(n)
        cases.append(dict(contract=contract, simulation=simulate(table, contract)))
    print(json.dumps(dict(cases_passed=len(cases), results=cases), indent=2))
