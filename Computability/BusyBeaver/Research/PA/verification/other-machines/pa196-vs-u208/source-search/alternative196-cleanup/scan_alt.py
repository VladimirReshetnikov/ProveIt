#!/usr/bin/env python3
"""Screen local single-state folds of the exact alternative196 table.

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
EXPECTED_HASH = 'aa05f079326ae244c725d611fd50f8ed1e4e9519907e28788dbb2172deee1b95'
DEFAULT_TABLE = (Path(__file__).resolve().parents[2] /
                 'jamesyc-upstream/pa196/data/pa196.tm')
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

def reaches_one_step(table, drop, keep, patch_read, patch, q, b, tape):
    """Return positive block length, or None if outside this finite template."""
    def project(x): return keep if x == drop else x
    w, d, n = table[q,b]
    goal = tape.copy(); goal[0] = w
    goal_head, goal_state = d, project(n)
    head, state, child = 0, keep, tape.copy()
    for k in range(1, MAX_STEPS+1):
        if state >= STATES or head not in child: return None
        row = (patch if patch is not None and state == keep
               and child[head] == patch_read else table[state,child[head]])
        w,d,n = row
        child[head] = w; head += d; state = project(n)
        if state == goal_state and head == goal_head and child == goal:
            return k
    return None

def unchanged_branch_may_work(table, drop, keep, changed, q, b, tape):
    """Sound prefilter: uncertainty (window or patched row) is kept."""
    def project(x): return keep if x == drop else x
    w,d,n = table[q,b]; goal = tape.copy(); goal[0] = w
    goal_head, goal_state = d, project(n)
    head, state, child = 0, keep, tape.copy()
    for _ in range(MAX_STEPS):
        if state >= STATES: return False
        if head not in child: return True
        if state == keep and child[head] == changed: return True
        w,d,n = table[state,child[head]]
        child[head] = w; head += d; state = project(n)
        if state == goal_state and head == goal_head and child == goal: return True
    return False

def screen(table, contexts):
    direct = []
    for drop in range(STATES):
        for keep in range(STATES):
            if keep == drop: continue
            if all(reaches_one_step(table,drop,keep,None,None,drop,b,t) is not None
                   for b in (0,1) for t in contexts[drop,b]):
                direct.append([drop,keep])
    pairs = []
    for drop in range(STATES):
        for keep in range(STATES):
            if keep == drop: continue
            for changed in (0,1):
                b = 1-changed
                if all(unchanged_branch_may_work(table,drop,keep,changed,drop,b,t)
                       for t in contexts[drop,b]):
                    pairs.append((drop,keep,changed))
    results = []; tested = 0
    for i,(drop,keep,changed) in enumerate(pairs):
        cases = [(q,b,t) for q in (drop,keep) for b in (changed,1-changed)
                 for t in contexts[q,b]]
        first = []
        for q,b,t in cases:
            if not any(q == x[0] and b == x[1] for x in first):
                first.append((q,b,t))
        for dest in range(STATES+1):
            if dest == drop: continue
            for w in (0,1):
                for d in (-1,1):
                    patch=(w,d,dest); tested += 1
                    if not all(reaches_one_step(table,drop,keep,changed,patch,q,b,t)
                               for q,b,t in first): continue
                    lengths = []
                    for q,b,t in cases:
                        k = reaches_one_step(table,drop,keep,changed,patch,q,b,t)
                        if k is None: break
                        lengths.append(k)
                    else:
                        results.append({'drop':drop,'keep':keep,'read':changed,
                                        'patch':[w,'R' if d==1 else 'L',dest],
                                        'block_lengths':sorted(set(lengths))})
        if (i+1)%10000 == 0:
            print(f'checked {i+1}/{len(pairs)} retained fold/read cases',flush=True)
    return direct, len(pairs), tested, results

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--table',type=Path,default=DEFAULT_TABLE)
    ap.add_argument('--output',type=Path,help='optional JSON receipt')
    ap.add_argument('--radius',type=int,default=2,help='blank-window closure radius (>= 2)')
    ap.add_argument('--invariant',choices=('two-predecessor','blank-window'),
                    default='two-predecessor',help='reachable-window overapproximation')
    args=ap.parse_args(); start=time.monotonic()
    table,digest=read_table(args.table); classes,seen=partition_and_reachability(table)
    if args.invariant == 'blank-window':
        contexts, may_halt, closure_size = blank_window_contexts(table,args.radius)
    else:
        contexts = incoming_contexts(table); may_halt = None; closure_size = None
    direct,kept,tested,results=screen(table,contexts)
    report={'table_sha256':digest,'working_states':STATES,'rows':len(table),
            'reachable_working_states':len(seen),'nontrivial_bisimulation_classes':classes,
            'window_offsets':WINDOW,'invariant':args.invariant,
            'closure_radius':args.radius if may_halt is not None else None,
            'closure_windows':closure_size,'abstract_halt_reachable':may_halt,
            'max_block_steps':MAX_STEPS,
            'contexts':sum(map(len,contexts.values())),
            'direct_keeper_folds':direct,'directed_fold_read_cases':STATES*(STATES-1)*2,
            'prefilter_survivors':kept,'one_row_patches_tested':tested,
            'one_row_patch_survivors':results,'elapsed_seconds':round(time.monotonic()-start,2)}
    data=json.dumps(report,indent=2)+'\n';print(data,end='')
    if args.output:args.output.write_text(data)

if __name__=='__main__':main()
