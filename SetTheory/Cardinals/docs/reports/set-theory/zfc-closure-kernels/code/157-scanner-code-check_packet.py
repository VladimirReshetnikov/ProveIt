#!/usr/bin/env python3
"""Replay the small literal-machine evidence without importing the runtime engine.

This verifies local experimental facts and explicit failed interfaces.  It does
NOT establish a <=217-state consistency machine.  The tape is a finite set of
one cells on an otherwise entirely zero, bi-infinite tape; equality therefore
compares the whole tape, including its exterior.
"""
from pathlib import Path
import hashlib
import json
import sys

ROOT = Path(__file__).resolve().parents[1]
PHY = (6, 2, 0, 4, 3, 7, 8, 5, 1)


def need(condition, message):
    if not condition:
        raise AssertionError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_table(path):
    table = {}
    for line in path.read_text().splitlines():
        if not line or line.startswith('#'):
            continue
        q, bit, write, move, nxt = line.split()
        q, bit, write, nxt = map(int, (q, bit, write, nxt))
        need((q, bit) not in table, 'Duplicate transition')
        need(bit in (0, 1) and write in (0, 1) and move in ('L', 'R'),
             'Nonbinary transition')
        table[q, bit] = write, -1 if move == 'L' else 1, nxt
    states = {q for q, _ in table}
    need(254 not in states, 'Terminal label has outgoing transitions')
    need(set(table) == {(q, b) for q in states for b in (0, 1)},
         'A working state lacks a binary transition')
    need(all(nxt == 254 or nxt in states for _, _, nxt in table.values()),
         'Unbound transition destination')
    return table, states


def frame(pc, logical, spares, gap=0, head=0):
    """Direct implementation of the documented frame encoding."""
    need(len(logical) == 9 and gap >= 0, 'Bad frame')
    physical = [0] * 9
    for i, slot in enumerate(PHY):
        physical[slot] = logical[i]
    cells = {head - 1, head + 64 + gap}
    cells.update(head + i for i, bit in enumerate(pc) if bit == '1')
    cursor = head + 65 + gap
    for value in physical + list(spares):
        need(type(value) is int and value >= 0, 'Non-natural register')
        cursor += 1
        cells.update(range(cursor, cursor + value + 1))
        cursor += value + 1
    return cells


def decode(q, head, cells):
    """Recognize a complete frame; an arbitrary visit to 84 is insufficient.

    The supplied sources have addresses shorter than 52 bits.  The header is
    therefore the first one at or right of head+52, and must be at least64 cells
    from the head.  Re-encoding at the end verifies every cell exactly.
    """
    if q != 84 or not cells or min(cells) != head - 1:
        return None
    right = [x for x in cells if x >= head + 52]
    if not right:
        return None
    header = min(right)
    if header < head + 64:
        return None
    end = max(cells)
    cursor = header + 1
    values = []
    while cursor < end:
        if cursor in cells or cursor + 1 not in cells:
            return None
        start = cursor + 1
        cursor = start
        while cursor in cells:
            cursor += 1
        values.append(cursor - start - 1)
    if cursor != end + 1 or len(values) < 10:
        return None
    offsets = sorted(x - head for x in cells if head <= x < head + 52)
    pc = ''.join('1' if i in offsets else '0'
                 for i in range(offsets[-1] + 1)) if offsets else ''
    logical = [values[slot] for slot in PHY]
    spares = values[9:]
    gap = header - head - 64
    if frame(pc, logical, spares, gap, head) != cells:
        return None
    return dict(pc=pc, logical_registers=logical, spares=spares, gap=gap,
                header=header, head=head)


def run(table, initial, limit, root_only=False):
    q, head, cells = initial
    cells = set(cells)
    intermediate_frames = 0
    for step in range(limit + 1):
        if step:
            decoded = decode(q, head, cells)
            if decoded is not None:
                if not root_only or decoded['pc'] == '':
                    return (q, head, cells), step, decoded, intermediate_frames
                intermediate_frames += 1
        if step == limit:
            raise AssertionError('No required complete frame within replay bound')
        bit = int(head in cells)
        need((q, bit) in table, ('Unexpected halt', step, q, head))
        write, move, nxt = table[q, bit]
        if write:
            cells.add(head)
        else:
            cells.discard(head)
        head += move
        q = nxt


def main():
    need(__debug__ and not sys.flags.optimize, 'Run with assertions enabled')
    provenance = json.loads((ROOT / 'inputs/provenance.json').read_text())
    for row in provenance['files']:
        need(digest(ROOT / row['file']) == row['sha256'], row['file'])

    named = [
        ('inputs/primary218.native.tm', 218),
        ('inputs/dominated218.native.tm', 218),
        ('experiments/rejected-short-scanner217.native.tm', 217),
        ('experiments/rejected-scanner-relay217.native.tm', 217),
        ('experiments/rejected-equality-relay220.native.tm', 220),
    ]
    tables = {}
    counts = []
    for name, expected_count in named:
        table, states = read_table(ROOT / name)
        need(len(states) == expected_count, ('State count', name, len(states)))
        tables[name] = table
        counts.append(dict(file=name, working_states=len(states),
                           transitions=len(table), sha256=digest(ROOT / name)))
    base = tables[named[0][0]]
    short = tables[named[2][0]]
    relay = tables[named[3][0]]
    remove50 = {key: value for key, value in base.items() if key[0] != 50}
    expected_short = dict(remove50)
    expected_short[34, 0] = (0, -1, 75)
    need(short == expected_short, 'Shortened-scanner patch is not exact')
    expected_relay = dict(remove50)
    expected_relay[34, 0] = (1, -1, 196)
    expected_relay[77, 1] = (0, -1, 75)
    need(relay == expected_relay, 'Temporary-marker relay patch is not exact')

    conf, ticks, seed, intermediate = run(short, (0, 0, set()), 110000,
                                          root_only=True)
    need(ticks == 104082, ('Startup length', ticks))
    need(conf[:2] == (84, -6), 'Startup state/head')
    need(seed['pc'] == '' and seed['gap'] == 6 and seed['header'] == 64,
         'Startup PC/gap/header')
    need(seed['logical_registers'] == [4, 3, 0, 0, 3, 0, 0, 0, 0],
         'Startup logical registers')
    need(seed['spares'] == [1] * 59 and len(conf[2]) == 139,
         'Startup spare list or whole tape')
    need(conf[2] == frame('', [4, 3, 0, 0, 3, 0, 0, 0, 0], [1] * 59, 6, -6),
         'Startup full-tape comparison')
    startup = dict(status='EXACT_FINITE_STARTUP_REPLAY', steps=ticks,
                   state=84, head=-6, one_cells=sorted(conf[2]),
                   earlier_complete_nonroot_frames=intermediate, **{
                       k: v for k, v in seed.items() if k != 'head'})

    sites = json.loads((ROOT / 'inputs/primary-sites.json').read_text())
    need(sites[40] == ['1101001001000000', 'CD', 1], 'Ordinal40 source')
    regs = [0] * 9
    initial = (84, 0, frame(sites[40][0], regs, [0]))
    wanted = (84, 0, frame('110100100100001', regs, [0]))
    old, oldsteps, oldframe, _ = run(base, initial, 10000)
    new, newsteps, newframe, _ = run(short, initial, 10000)
    need(old == wanted and oldsteps == 588, 'Reference interface replay')
    need(new == (84, 0, frame('1101001001001', regs, [0])) and newsteps == 662,
         'Rejected interface counterexample')
    need(new != wanted, 'Missing counterexample')
    counterexample = dict(status='EXACT_FAILED_INTERFACE', ordinal=40,
                         initial_pc=sites[40][0], initial_registers=regs,
                         expected_steps=oldsteps, actual_steps=newsteps,
                         expected=oldframe, actual=newframe,
                         expected_one_cells=sorted(old[2]),
                         actual_one_cells=sorted(new[2]),
                         scope='A complete valid input frame; not a claim that '
                               'this frame occurs on the blank execution.')
    result = dict(status='PACKET_LITERAL_EVIDENCE_PASS',
                  verified_217_state_consistency_machine=False,
                  repository_commit=provenance['commit'], tables=counts,
                  exact_patches_checked=True, short_scanner_startup=startup,
                  short_scanner_counterexample=counterexample)
    out = ROOT / 'verification'
    out.mkdir(exist_ok=True)
    (out / 'packet.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k not in
                      ('short_scanner_startup', 'short_scanner_counterexample')},
                     indent=2))
    print('Blank startup:104082 steps; ordinal40 counterexample:588 vs662 steps.')


if __name__ == '__main__':
    main()
