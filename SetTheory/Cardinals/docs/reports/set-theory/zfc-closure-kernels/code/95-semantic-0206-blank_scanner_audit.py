#!/usr/bin/env python3
"""Find an exact source-contract failure on a mutant's own blank-tape run.

This is finite executable arithmetic, not a conclusion about eventual halting.
No inherited Python module is imported. All coordinates of every checkpoint
tape are retained in the output. The full blank prefix is replayed densely.
"""
import argparse
from collections import deque
import hashlib
import json
from pathlib import Path

from reachability import successors

PHYSICAL = (6, 2, 0, 4, 3, 7, 8, 5, 1)


def read_table(path):
    rows = {}
    for line in path.read_text().splitlines():
        if not line or line.startswith('#'):
            continue
        q, bit, write, direction, target = line.split()
        q, bit, write, target = map(int, (q, bit, write, target))
        assert bit in (0, 1) and write in (0, 1) and direction in ('L', 'R')
        assert (q, bit) not in rows
        rows[q, bit] = (write, 1 if direction == 'R' else -1, target)
    return rows


def parse_frame(state, head, ones):
    if state != 96 or not ones or min(ones) != head - 1:
        return None
    beyond = [x for x in ones if x >= head + 52]
    if not beyond:
        return None
    header = min(beyond)
    if header < head + 64:
        return None
    at, last, values = header + 1, max(ones), []
    while at <= last:
        if at in ones or at + 1 not in ones:
            return None
        start = at + 1
        at = start
        while at in ones:
            at += 1
        values.append(at - start - 1)
    if len(values) < 10 or at != last + 1:
        return None
    pc = ''.join('1' if x in ones else '0' for x in range(head, header)).rstrip('0')
    if len(pc) > 51:
        return None
    return dict(pc=pc, registers=[values[i] for i in PHYSICAL],
                spares=values[9:], head=head, header=header,
                distance=header-head, all_one_positions=sorted(ones))


def make_frame(pc, regs, spares, head, header):
    physical = [None] * 9
    for r, j in enumerate(PHYSICAL):
        physical[j] = regs[r]
    assert header-head >= len(pc)
    ones = {head-1, header} | {head+i for i, c in enumerate(pc) if c == '1'}
    at = header+1
    for v in physical + spares:
        at += 1
        ones.update(range(at, at+v+1))
        at += v+1
    return ones


def expected(frame, site):
    pc, op, reg = site
    values, spares = frame['registers'][:], frame['spares'][:]
    if op == 'CH':
        return None
    positive = op == 'CD' and values[reg] > 0
    nxt = successors(pc, op, reg)[int(positive) if op == 'CD' else 0]
    shift = int(op in ('CI', 'CD', 'CB') and nxt != '' and '1' not in nxt)
    # If a shortened empty pointer overflows, its result is also empty.
    if op in ('CD', 'CB') and not positive:
        count = reg if op == 'CB' else 1
        base = pc
        for _ in range(count):
            j = base.rfind('0')
            base = base[:j] if j >= 0 else ''
        shift = int('0' not in base)
    if op == 'CI' or positive:
        shift = int('0' not in pc)
    if op == 'CI':
        values[reg] += 1
        spares.append(1)
    elif positive:
        values[reg] -= 1
    h = frame['head'] - shift
    header = frame['header'] + int(positive)
    ones = make_frame(nxt, values, spares, h, header)
    return parse_frame(96, h, ones)


def dense_replay(table, ticks):
    # This interpreter uses an array tape and indexed rows, unlike sparse run.
    width = 2*ticks+3
    tape = bytearray(width)
    origin, pos, state = ticks+1, ticks+1, 95
    tab = [None] * (2*(max(q for q, b in table)+1))
    for (q, b), row in table.items():
        tab[2*q+b] = row
    for _ in range(ticks):
        w, move, state = tab[2*state+tape[pos]]
        tape[pos] = w
        pos += move
    return state, pos-origin, [i-origin for i, b in enumerate(tape) if b]


def audit(table, sites, max_binary=5000000, max_instructions=500):
    leaf_index = {p: i for i, (p, op, reg) in enumerate(sites)}
    def lookup(pc):
        bits = pc + '0'*51
        for n in range(1, 52):
            if bits[:n] in leaf_index:
                assert '1' not in pc[n:]
                return leaf_index[bits[:n]]
        raise ValueError(pc)
    q, head, ones = 95, 0, set()
    initial = previous = want = None
    completed, last_tick = 0, 0
    recent = deque(maxlen=12)
    for tick in range(max_binary+1):
        frame = parse_frame(q, head, ones) if q == 96 else None
        if frame and (initial is not None or frame['pc'] == ''):
            if initial is None:
                initial = dict(binary_steps=tick, **frame)
            elif tick > last_tick:
                if frame != want:
                    dense = dense_replay(table, tick)
                    assert dense == (q, head, sorted(ones))
                    return dict(status='ACTUAL_BLANK_REACHABLE_CONTRACT_FAILURE',
                        initialized=initial, completed_source_steps=completed,
                        entry_binary_steps=last_tick, exit_binary_steps=tick,
                        failing_site=sites[lookup(previous['pc'])],
                        failing_site_index=lookup(previous['pc']),
                        input_frame=previous, expected_frame=want, actual_frame=frame,
                        differing_cells=sorted(set(want['all_one_positions']) ^ ones),
                        recent=list(recent), independent_dense_blank_replay=True)
                completed += 1
                if completed == max_instructions:
                    dense = dense_replay(table, tick)
                    assert dense == (q, head, sorted(ones))
                    return dict(status='FINITE_PREFIX_PASS', initialized=initial,
                                completed_source_steps=completed, binary_steps=tick,
                                final_frame=frame, independent_dense_blank_replay=True)
            previous, last_tick = frame, tick
            i = lookup(frame['pc'])
            want = expected(frame, sites[i])
            recent.append(dict(binary_steps=tick, source_steps=completed,
                               site_index=i, site=sites[i], registers=frame['registers']))
            if want is None:
                return dict(status='SOURCE_HALT_SITE_REACHED', binary_steps=tick)
        if tick == max_binary:
            return dict(status='LIMIT', bound=max_binary, initialized=initial,
                        completed_source_steps=completed)
        b = int(head in ones)
        if (q, b) not in table:
            return dict(status='BINARY_HALT', binary_steps=tick, initialized=initial)
        write, move, q = table[q, b]
        if write:
            ones.add(head)
        else:
            ones.discard(head)
        head += move


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--table', type=Path, required=True)
    ap.add_argument('--sites', type=Path, required=True)
    ap.add_argument('--shorten', action='store_true')
    ap.add_argument('--instructions', type=int, default=500)
    ap.add_argument('--limit', type=int, default=5000000)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    tab = read_table(args.table)
    if args.shorten:
        assert tab[41, 0] == (0, -1, 58)
        assert tab[58, 0] == (0, -1, 84)
        tab[41, 0] = (0, -1, 84)
        del tab[58, 0], tab[58, 1]
    result = audit(tab, json.loads(args.sites.read_text()), args.limit, args.instructions)
    result['table_input_sha256'] = hashlib.sha256(args.table.read_bytes()).hexdigest()
    result['scanner_mutation'] = args.shorten
    result['scope'] = ('Finite exact failure or validation of the one-source-instruction contract '
                       'at the next qualifying dispatcher return. No conclusion about eventual '
                       'halting, later matching frames, or all possible simulation relations.')
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in
                     ('initialized','input_frame','expected_frame','actual_frame','final_frame','recent')}, indent=2))
    if result.get('initialized'):
        print('INITIAL', {k:v for k,v in result['initialized'].items()
                          if k not in ('spares', 'all_one_positions')})
    if result.get('actual_frame'):
        print('EXPECTED', {k:v for k,v in result['expected_frame'].items()
                           if k not in ('spares', 'all_one_positions')})
        print('ACTUAL', {k:v for k,v in result['actual_frame'].items()
                         if k not in ('spares', 'all_one_positions')})


if __name__ == '__main__':
    if not __debug__:
        raise SystemExit('Assertions must be enabled.')
    main()
