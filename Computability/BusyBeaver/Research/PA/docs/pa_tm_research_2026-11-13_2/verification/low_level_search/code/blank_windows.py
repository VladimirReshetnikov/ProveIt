#!/usr/bin/env python3
"""Screen local single-state folds of jamesyc's exact PA196 table.

See README.md for the proof obligation and explicit scope; a negative result
is not a lower bound. Only Python's standard library is required.
"""
from __future__ import annotations
import argparse
import hashlib
import itertools
import json
import time
from collections import defaultdict, deque
from pathlib import Path

STATES = 196
EXPECTED_HASH = 'e8bbccd4cfa325251ca95066db116b5aa766e404b0971c33c02772be1c3617a8'
DEFAULT_TABLE = Path(__file__).resolve().parents[1] / 'inputs/baseline196.tm'
MAX_STEPS = 16
WINDOW = (-2, -1, 0, 1, 2)

def read_table(path):
    content = path.read_bytes()
    digest = hashlib.sha256(content).hexdigest()
    if digest != EXPECTED_HASH:
        raise ValueError(f'Unexpected table hash: {digest}')
    table = {}
    for line in content.decode('ascii').splitlines():
        line = line.split('#', 1)[0].strip()
        if not line:
            continue
        q, b, w, d, t = line.split()
        q, b, w, t = int(q), int(b), int(w), int(t)
        if not (0 <= q < STATES and b in (0, 1) and w in (0, 1)
                and d in ('L', 'R') and 0 <= t <= STATES):
            raise ValueError(f'Invalid transition {line}')
        if (q,b) in table:
            raise ValueError(f'Duplicate row {q}, {b}')
        table[q,b] = (w, 1 if d == 'R' else -1, t)
    if set(table) != set(itertools.product(range(STATES), range(2))):
        raise ValueError('Transition domain is not 196 × 2')
    return table, digest

def partition_and_reachability(table):
    cls = [0] * STATES + [1]
    while True:
        ids, new = {}, []
        for q in range(STATES + 1):
            key = ('halt',) if q == STATES else tuple(
                (w,d,cls[t]) for w,d,t in (table[q,0], table[q,1]))
            new.append(ids.setdefault(key,len(ids)))
        if len(set(new)) == len(set(cls)):
            cls = new
            break
        cls = new
    classes = defaultdict(list)
    for q,c in enumerate(cls): classes[c].append(q)
    seen, queue = {0}, deque([0])
    while queue:
        q = queue.popleft()
        for b in (0,1):
            t = table[q,b][2]
            if t < STATES and t not in seen:
                seen.add(t); queue.append(t)
    return [v for v in classes.values() if len(v)>1], sorted(seen)

def incoming_contexts(table):
    incoming = defaultdict(list)
    for (q,b),(w,d,t) in table.items():
        if t < STATES:
            incoming[t].append((-d,w,q,b))
    contexts = {}
    for q in range(STATES):
        for b in (0,1):
            cases = []
            for bits in itertools.product(range(2), repeat=4):
                tape = dict(zip((-2,-1,1,2),bits)); tape[0] = b
                if q == 0:
                    cases.append(tape)
                    continue
                for pos,w,p,read in incoming[q]:
                    if tape[pos] != w: continue
                    # The predecessor may have been the initial state.
                    if p == 0:
                        cases.append(tape); break
                    previous = tape.copy(); previous[pos] = read
                    if any(previous[pos+pos2] == w2
                           for pos2,w2,_,_ in incoming[p]):
                        cases.append(tape); break
            contexts[q,b] = cases
    return contexts

def blank_window_contexts(table, radius=2):
    """Least blank-start window closure, forgetting each newly entered bit."""
    if radius < 2: raise ValueError('radius must be at least 2')
    width = 2 * radius + 1; mask = (1 << width) - 1; middle = 1 << radius
    seen = {(0,0)}; queue = deque(seen); may_halt = False
    while queue:
        q,bits = queue.popleft()
        read = (bits >> radius) & 1
        write,direction,target = table[q,read]
        bits = (bits | middle) if write else (bits & ~middle)
        if target == STATES:
            may_halt = True
            continue
        for fresh in (0,1):
            shifted = ((bits >> 1) | (fresh << (width-1)) if direction == 1
                       else ((bits << 1) & mask) | fresh)
            pair = (target,shifted)
            if pair not in seen:
                seen.add(pair); queue.append(pair)
    contexts = {(q,b): [] for q in range(STATES) for b in (0,1)}
    projected = {(q, (bits >> (radius - 2)) & 31) for q,bits in seen}
    for q,bits in sorted(projected):
        tape = {i:(bits >> (i+2)) & 1 for i in WINDOW}
        contexts[q,tape[0]].append(tape)
    return contexts, may_halt, len(seen)
