#!/usr/bin/env python3
"""Check the finite local proof of candidate 1's global tape simulation.

The proof uses no source-program or register-frame assumptions.  A tape outside
each explicitly constrained finite window is an opaque arbitrary function.
The incoming-edge proof establishes an inductive condition from state 95 on
every tape.  The five instruction families give positive bounded stuttering at
checkpoints excluding old labels 92 and 122.
"""
from pathlib import Path
from itertools import product
import hashlib
import json

HERE = Path(__file__).resolve().parent
BASE = HERE/'reference/zfc245_old.tm'
CANDIDATE = HERE/'candidate_1_244_old.tm'

def read(path):
    rows={}
    start=None
    for line in path.read_text().splitlines():
        if line.startswith('#! start '):
            start=int(line.split()[-1])
        if not line or line.startswith('#'):
            continue
        q,b,w,d,t=line.split()
        key=int(q),int(b)
        assert key not in rows
        rows[key]=int(w), (1 if d=='R' else -1), int(t)
    return rows,start

def invariant(q,tape,head=0):
    if q in (68,122,167):
        return tape[head-1]==1
    if q==81:
        return tape[head-1]==0 or tape[head-2]==1
    return True

def invariant_check(table):
    # Every target invariant can mention at most head-2 after an L/R move.
    # Thus cells -3 through 1 contain every variable in the one-step formula.
    coordinates=list(range(-3,2))
    checked=0
    for q in sorted({q for q,b in table}):
        for bits in product((0,1),repeat=len(coordinates)):
            tape=dict(zip(coordinates,bits))
            if not invariant(q,tape):
                continue
            write,direction,target=table[q,tape[0]]
            tape[0]=write
            assert invariant(target,tape,direction),(q,bits,target)
            checked+=1
    assert invariant(95,{})
    entries={str(t):[[q,b,w,d] for (q,b),(w,d,u) in sorted(table.items()) if u==t]
             for t in (68,81,122,167)}
    assert entries=={
        '68':[[52,1,1,1],[123,1,1,1]],
        '81':[[68,1,1,1],[123,0,0,1]],
        '122':[[104,1,1,1],[106,1,1,1]],
        '167':[[145,1,1,1],[148,1,1,1]],
    }
    return dict(status='PASS',
                quantified_tape='Every function from integer cells to binary symbols',
                finite_formula_coordinates=coordinates,checked_truth_table_implications=checked,
                formulas={'68':'T(h-1)=1','81':'T(h-1)=1 implies T(h-2)=1',
                          '122':'T(h-1)=1','167':'T(h-1)=1'},
                initial_state=95,initial_invariant_vacuous=True,
                complete_incoming_rows=entries)

def run_window(table,start,window,steps):
    tape=dict(window)
    q,h=start,0
    trace=[]
    for _ in range(steps):
        assert h in tape,('Opaque outside context was read',q,h,tape)
        symbol=tape[h]
        w,d,t=table[q,symbol]
        trace.append(dict(state=q,head=h,read=symbol,row=[w,d,t]))
        tape[h]=w
        h+=d
        q=t
    return q,h,tape,trace

def main():
    assert __debug__
    old,start=read(BASE)
    new,newstart=read(CANDIDATE)
    assert start==newstart==95
    oldstates={q for q,b in old}
    newstates={q for q,b in new}
    assert len(oldstates)==245 and newstates==oldstates-{122}
    assert set(new)=={(q,b) for q in newstates for b in (0,1)}
    assert {t for w,d,t in new.values()}-newstates=={254}
    changed={key:(old[key],new[key]) for key in new if old[key]!=new[key]}
    assert changed=={
        (92,1):((1,-1,24),(1,1,66)),
        (104,1):((1,1,122),(1,1,92)),
        (106,1):((1,1,122),(1,1,92)),
        (167,1):((1,-1,92),(1,-1,151)),
    }
    inv=invariant_check(old)
    excluded={92,122}
    grouped={(104,1),(106,1),(167,1),(81,1)}
    common=[]
    for key in sorted(old):
        q,b=key
        if q in excluded or key in grouped:
            continue
        assert old[key]==new[key]
        assert old[key][2] not in excluded
        common.append(key)
    assert len(common)==482
    macros=[]
    families=[]
    for q in (104,106):
        for b in (0,1):
            families.append((f'enter122_from{q}_read{b}',q,{0:1,1:b},2,4 if b==0 else 2))
    families += [
        ('repair167',167,{-1:1,0:1},2,2),
        ('enter92_from81_zero',81,{-1:0,0:1},2,2),
        ('enter92_from81_one',81,{-2:1,-1:1,0:1},6,4),
    ]
    for name,q,window,oldsteps,newsteps in families:
        left=run_window(old,q,window,oldsteps)
        right=run_window(new,q,window,newsteps)
        assert left[:3]==right[:3],(name,left,right)
        assert left[0] not in excluded and left[0] in oldstates
        assert oldsteps>0 and newsteps>0
        macros.append(dict(name=name,start=q,known_input_cells=window,
                           old_steps=oldsteps,new_steps=newsteps,
                           end_state=left[0],end_head=left[1],
                           known_output_cells=left[2],
                           old_trace=left[3],new_trace=right[3],
                           arbitrary_outside_context_preserved=True))
    result=dict(status='PASS_GLOBAL_CONTEXTUAL_SIMULATION',
        old_table_sha256=hashlib.sha256(BASE.read_bytes()).hexdigest(),
        new_table_sha256=hashlib.sha256(CANDIDATE.read_bytes()).hexdigest(),
        old_working_states=245,new_working_states=244,initial_state=95,halt_state=254,
        invariant=inv,excluded_checkpoint_states=sorted(excluded),
        ordinary_common_rows=len(common),macro_entry_rows=[list(k) for k in sorted(grouped)],
        macro_families=macros,
        theorem='For every initial binary tape and head position, execution from state95 of these two exact tables has the same halting outcome.',
        justification='Induct on old checkpoint visits using the globally inductive local tape condition. Each common step or guarded macro reaches an identical tape, head and checkpoint state in both machines. Old and new block clocks are positive and at most6, so either computation halts exactly when the other does.',
        proof_scope='Finite Boolean implication enumeration plus literal finite-window identities; a mathematical proof checker, not a proof-assistant kernel endpoint.')
    (HERE/'contextual_fold_proof.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('invariant','macro_families')},indent=2))

if __name__=='__main__':
    main()
