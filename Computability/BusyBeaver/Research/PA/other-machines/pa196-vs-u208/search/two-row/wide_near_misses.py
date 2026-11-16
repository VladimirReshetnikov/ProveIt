#!/usr/bin/env python3
"""Examine four PA196 local-fold near misses with wider windows and full tapes."""
from __future__ import annotations
import argparse
import hashlib
import importlib.util
import json
from collections import Counter, deque
from pathlib import Path

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('pa196_local_folds', HERE.parent / 'scan_local_folds.py')
fold = importlib.util.module_from_spec(spec)
spec.loader.exec_module(fold)

# Two directions of each state identification produce the same projected table
# up to state names. A row is (written bit, head displacement, target state).
CANDIDATES = ((56,96,(0,1,59),(1,1,67)), (96,56,(0,1,59),(1,1,67)),
              (96,103,(0,1,59),(1,1,110)), (103,96,(0,1,59),(1,1,110)))
RADIUS = 6
WIDTH = 2*RADIUS+1
MASK = (1<<WIDTH)-1
CENTER = 1<<RADIUS

def require(condition, message):
    if not condition: raise ValueError(message)

def closure(table):
    found={(0,0)}
    queue=deque(found)
    halting=False
    while queue:
        q,tape=queue.popleft()
        write,direction,target=table[q,(tape>>RADIUS)&1]
        tape=(tape & ~CENTER) | (write<<RADIUS)
        if target==196:
            halting=True
            continue
        for bit in (0,1):
            shifted=((tape>>1)|(bit<<(WIDTH-1))) if direction==1 else (((tape<<1)&MASK)|bit)
            pair=(target,shifted)
            if pair not in found:
                found.add(pair)
                queue.append(pair)
    return found,halting

def window_block(table,candidate,q,tape):
    """Follow one candidate block until a match, escape, loop, or 128 steps."""
    drop,keep,row0,row1=candidate
    proj=lambda s:keep if s==drop else s
    w,d,n=table[q,(tape>>RADIUS)&1]
    goal=(proj(n),d,(tape&~CENTER)|(w<<RADIUS))
    state,head,current=keep,0,tape
    seen=set()
    for k in range(128):
        if state==196:return 'halt',k
        if not -RADIUS<=head<=RADIUS:return 'outside',k
        triple=(state,head,current)
        if triple in seen:return 'loop',k
        seen.add(triple)
        b=(current>>(head+RADIUS))&1
        w,d,n=(row1 if b else row0) if state==keep else table[state,b]
        current=(current&~(1<<(head+RADIUS)))|(w<<(head+RADIUS))
        state,head=proj(n),head+d
        if (state,head,current)==goal:return 'match',k+1
    return 'step-limit',128

def blank_tail_counterexample(table,candidate):
    """Verify an exact full-tape prefix to an obviously infinite right sweep."""
    drop,keep,row0,row1=candidate
    proj=lambda s:keep if s==drop else s
    mask=203
    tape={i-RADIUS for i in range(WIDTH) if (mask>>i)&1}  # all other cells zero
    source_state=96
    read=int(0 in tape)
    w,d,n=table[source_state,read]
    goal_tape=set(tape)
    if w:goal_tape.add(0)
    else:goal_tape.discard(0)
    goal=(proj(n),d,goal_tape)
    state,head=keep,0
    trace=[]
    require(drop!=35 and keep!=35 and table[35,0]==(1,1,35), 'right sweep row was changed')
    require(goal[0]!=35, 'goal could be reached during sweep')
    for k in range(129):
        if state==35 and all(cell<head for cell in tape):
            return {'parent_state':source_state,'window_mask':mask,
                    'initial_one_cells':[-6,-5,-3,0,1], 'parent_one_step_state':goal[0],
                    'sweep_start_step':k, 'sweep_head':head, 'sweep_state':35,
                    'sweep_row':[1,'R',35], 'trace':trace}
        require(k<128 and state!=196, 'no certified sweep within finite prefix')
        b=int(head in tape)
        w,d,n=(row1 if b else row0) if state==keep else table[state,b]
        trace.append([state,head,b,w,'R' if d==1 else 'L',proj(n)])
        if w:tape.add(head)
        else:tape.discard(head)
        state,head=proj(n),head+d
        require((state,head,tape)!=goal, 'candidate matched parent before sweep')
    raise ValueError('no sweep')

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    table,table_sha=fold.read_table(fold.DEFAULT_TABLE)
    seen,may_halt=closure(table)
    require(len(seen)==270067 and may_halt and (96,203) in seen,
            'unexpected abstract closure or missing common context')
    result=[]
    for candidate in CANDIDATES:
        drop,keep,_,_=candidate
        counts=Counter()
        examples={}
        for q in (drop,keep):
            for state,tape in sorted(seen):
                if state!=q:continue
                outcome,steps=window_block(table,candidate,q,tape)
                counts[outcome]+=1
                examples.setdefault(outcome,{'state':q,'window_mask':tape,'steps':steps})
        sweep=blank_tail_counterexample(table,candidate)
        result.append({'drop':drop,'keep':keep,'counts':dict(sorted(counts.items())),
                       'examples':examples,'blank_tail_extension_counterexample':sweep})
    data={'table_sha256':table_sha,'radius':RADIUS,'closure_windows':len(seen),
          'abstract_halt_reachable':may_halt,'max_child_steps':128,
          'context_96_mask_203_in_abstract_closure':True,'candidates':result,
          'actual_blank_reachability_of_counterexample_not_established':True}
    text=json.dumps(data,indent=2,sort_keys=True)+'\n'
    print(text,end='')
    if args.output:args.output.write_text(text)

if __name__=='__main__': main()
