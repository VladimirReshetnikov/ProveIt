#!/usr/bin/env python3
"""Reproduce the bounded local search which discovered the 242-state fold.

Sound finite abstraction: radius4 tape windows, seeded with every window at
state95. Missing boundary bits are both possibilities. Each candidate is tested
against EVERY window in this inductive over-approximation. Positive results
are finite-premise simulation certificates; failures are only failures of the
specified local coalescence search, never lower bounds on Turing-machine size.

Search modes: (0) redirect p to q, ≤30 steps per side; (1,2,3) additionally
replace q's zero row, one row, or both rows by p's corresponding original rows,
≤24 steps per side. Both source contexts must coalesce when q is altered.
No reads outside the represented window are allowed; equal endpoints preserve
the entire tape because no other cell was read or written.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import sys
import time
from pathlib import Path
# Resolve the bundled parser explicitly when Python is run in isolated mode.
sys.path.insert(0, str(Path(__file__).resolve().parent))
from prove_zero_reuse242 import read_table

def abstract_reach(table, start, states, halt, radius):
    width = 2*radius+1
    count = 1 << width
    mask = count-1
    reach = {q: bytearray(count) for q in states | {halt}}
    queue = [(start, p) for p in range(count)]
    reach[start][:] = b'\1'*count
    cursor = 0
    while cursor < len(queue):
        q, p = queue[cursor]
        cursor += 1
        if q == halt:
            continue
        w, d, target = table[q, (p >> radius) & 1]
        written = (p & ~(1 << radius)) | (w << radius)
        if d == 1:
            shifted, unknown = written >> 1, 1 << (2*radius)
        else:
            shifted, unknown = (written << 1) & mask, 1
        for next_pattern in (shifted, shifted | unknown):
            if not reach[target][next_pattern]:
                reach[target][next_pattern] = 1
                queue.append((target, next_pattern))
    return {q: [p for p, bit in enumerate(bits) if bit] for q, bits in reach.items()}, len(queue)

def old_traces(table, patterns, halt, radius, limit):
    stride, space = 2*radius+3, 1 << (2*radius+1)
    traces = {}
    for state, pats in patterns.items():
        if state == halt:
            continue
        trajectories = []
        for pattern in pats:
            q, h, tape, frames = state, 0, pattern, set()
            for step in range(limit+1):
                frames.add((q*stride + h+radius+1)*space + tape)
                if q == halt or abs(h) > radius:
                    break
                w, d, q = table[q, (tape >> (h+radius)) & 1]
                tape = (tape & ~(1 << (h+radius))) | (w << (h+radius))
                h += d
            trajectories.append(frames)
        traces[state] = trajectories
    return traces

def coalesces(table, q, pattern, remove, keep, rows, excluded, old_frames,
              halt, radius, limit):
    h, tape = 0, pattern
    stride, space = 2*radius+3, 1 << (2*radius+1)
    for step in range(limit+1):
        if q not in excluded and ((q*stride+h+radius+1)*space+tape) in old_frames:
            return True
        if q == halt or abs(h) > radius:
            return False
        b = (tape >> (h+radius)) & 1
        w, d, target = rows[b] if q == keep else table[q, b]
        tape = (tape & ~(1 << (h+radius))) | (w << (h+radius))
        h += d
        q = keep if target == remove else target
    return False

def main():
    if not __debug__:
        raise RuntimeError('Assertions must be enabled.')
    ap = argparse.ArgumentParser()
    ap.add_argument('baseline', type=Path)
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--radius', type=int, default=4)
    args = ap.parse_args()
    started = time.monotonic()
    table, start, states, halt = read_table(args.baseline)
    patterns, abstract_count = abstract_reach(table, start, states, halt, args.radius)
    unread = [[q, b] for q in sorted(states) for b in (0, 1)
              if not any(((p >> args.radius) & 1) == b for p in patterns[q])]
    mode_records = []
    for modes, limit in (([0], 30), ([1, 2, 3], 24)):
        traces = old_traces(table, patterns, halt, args.radius, limit)
        tested, accepted = 0, []
        for remove in sorted(states - {start}):
            for keep in sorted(states - {remove}):
                if keep == start and modes != [0]:
                    continue
                for mode in modes:
                    rows = [table[remove if mode & (1 << b) else keep, b] for b in (0, 1)]
                    tested += 1
                    excluded = {remove, keep} if mode else {remove}
                    entry_states = (remove, keep) if mode else (remove,)
                    ok = True
                    for entry in entry_states:
                        for index, pattern in enumerate(patterns[entry]):
                            if not coalesces(table, keep, pattern, remove, keep,
                                             rows, excluded, traces[entry][index],
                                             halt, args.radius, limit):
                                ok = False
                                break
                        if not ok:
                            break
                    if ok:
                        accepted.append(dict(delete=remove, retain=keep, mode=mode,
                                             replacement_retained_rows=rows))
        mode_records.append(dict(modes=modes, max_steps_per_side=limit,
                                 candidate_tests=tested, accepted=accepted))
        print(json.dumps(mode_records[-1]), flush=True)
    record = dict(status='COMPLETED_RESTRICTED_LOCAL_SEARCH',
        baseline_sha256=hashlib.sha256(args.baseline.read_bytes()).hexdigest(),
        radius=args.radius, start=start, initial_windows='all binary windows',
        abstract_configurations=abstract_count, unread_rows=unread,
        search=mode_records, elapsed_seconds=time.monotonic()-started,
        scope='No lower bound or minimality claim; row-replacement modes and '
              'within-window coalescence only. The selected positive result has '
              'a separate simpler invariant and proof checker.')
    args.output.write_text(json.dumps(record, indent=2)+'\n')
    print(json.dumps({'output': str(args.output), 'elapsed_seconds': record['elapsed_seconds']}))

if __name__ == '__main__':
    main()
