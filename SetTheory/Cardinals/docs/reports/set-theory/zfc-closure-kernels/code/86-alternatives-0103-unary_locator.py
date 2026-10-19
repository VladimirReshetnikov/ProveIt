#!/usr/bin/env python3
"""18-state literal binary indexed-record locator with one destructive counter.

Prepared layout: 1^(i+1) 0000 1 0 [records], each record having three
nonempty unary fields separated by 0. Erase the first 1 of the first record.
Start on the rightmost counter 1. Return immediately after the erased first
1 of record i. The counter becomes 1 and the gap grows by i zeroes.

17 operational states + 1 totalizing nonhalting rejection state; one separate
return/halt label. This is a locator component, not a complete proof checker.
"""
from pathlib import Path
if not __debug__:
    raise RuntimeError('Assertions must be enabled; do not use python -O.')


import json,itertools,hashlib,random

NAMES=['counter','check','gap_advance','anchor_advance','first_advance','ones_advance',
       'skip_tag','skip_left','skip_right','mark_next','return_ones','return_zero',
       'restore_zero_counter','gap_done','anchor_done','first_done','ones_done','reject']
IDS={n:i for i,n in enumerate(NAMES)}
RETURN=len(NAMES)

def compile_locator():
    rows={}
    def put(q,b,w,d,n):rows[IDS[q],b]=(w,d,RETURN if n=='RETURN' else IDS[n])
    def both(q,actions):
        for b,(w,d,n) in enumerate(actions):put(q,b,w,d,n)
    both('counter',[(0,'L','counter'),(0,'L','check')])
    both('check',[(0,'R','restore_zero_counter'),(1,'R','gap_advance')])
    for mode in ('advance','done'):
        both('gap_'+mode,[(0,'R','gap_'+mode),(1,'R','anchor_'+mode)])
        both('anchor_'+mode,[(0,'R','first_'+mode),(1,'R','reject')])
        if mode=='advance': both('first_'+mode,[(1,'R','skip_tag'),(1,'R','ones_'+mode)])
        else: both('first_'+mode,[(0,'R','RETURN'),(1,'R','ones_'+mode)])
        both('ones_'+mode,[(0,'R','first_'+mode),(1,'R','ones_'+mode)])
    both('skip_tag',[(0,'R','skip_left'),(1,'R','skip_tag')])
    both('skip_left',[(0,'R','skip_right'),(1,'R','skip_left')])
    both('skip_right',[(0,'R','mark_next'),(1,'R','skip_right')])
    both('mark_next',[(0,'R','reject'),(0,'L','return_ones')])
    both('return_ones',[(0,'L','return_zero'),(1,'L','return_ones')])
    both('return_zero',[(0,'L','counter'),(1,'L','return_ones')])
    both('restore_zero_counter',[(1,'R','gap_done'),(1,'R','reject')])
    both('reject',[(0,'R','reject'),(1,'R','reject')])
    assert len(rows)==2*len(NAMES)
    return rows


def frame(i,records,gap=4):
    assert gap>=2 and records and 0<=i<len(records)
    assert all(len(r)==3 and all(type(v) is int and v>=0 for v in r) for r in records)
    tape={p:1 for p in range(-i,1)}
    anchor=gap+1;tape[anchor]=1;x=anchor+2;starts=[]
    for r in records:
        starts.append(x)
        for val in r:
            for p in range(x,x+val+1):tape[p]=1
            x+=val+2
    tape.pop(starts[0]);return tape,starts


def execute(table,tape,limit=1000000):
    tape=dict(tape);q=IDS['counter'];h=0;steps=0
    while q!=RETURN:
        if steps>=limit:raise RuntimeError('fuel exhausted')
        w,d,q=table[q,tape.get(h,0)]
        if w:tape[h]=w
        else:tape.pop(h,None)
        h+=1 if d=='R' else -1;steps+=1
    return tape,h,steps


def check(table,i,records,gap):
    tape,starts=frame(i,records,gap)
    expected=dict(tape)
    expected[starts[0]]=1;expected.pop(starts[i],None)
    for p in range(-i+1,1):expected.pop(p,None)
    actual,head,steps=execute(table,tape)
    assert actual==expected,(i,records,gap,actual,expected)
    assert head==starts[i]+1
    return steps


def main():
    table=compile_locator();count=0;max_steps=0
    vals=list(itertools.product(range(3),repeat=3))
    for length in (1,2,3):
        # All small records for length 1/2; diagonal structured cases for 3.
        tests=itertools.product(vals,repeat=length) if length<3 else ((a,b,a) for a in vals for b in vals)
        for records in tests:
            for i in range(length):
                for gap in (2,4,7):
                    max_steps=max(max_steps,check(table,i,list(records),gap));count+=1
    rng=random.Random(24618)
    for trial in range(1000):
        records=[tuple(rng.randrange(100) for j in range(3)) for k in range(rng.randrange(1,40))]
        i=rng.randrange(len(records));gap=rng.randrange(2,80)
        max_steps=max(max_steps,check(table,i,records,gap));count+=1
    path=Path(__file__).parent/'unary_locator_18.tm'
    lines=[f'# working_states={RETURN}; start={IDS["counter"]}; halt={RETURN}', '# q read write move next']
    for (q,b),(w,d,n) in sorted(table.items()):lines.append(f'{q} {b} {w} {d} {n}')
    path.write_text('\n'.join(lines)+'\n')
    result={'scope':'Prepared-frame destructive indexed-record locator component, not complete search TM',
      'working_states':RETURN,'operational_states':RETURN-1,'totalizing_rejection_states':1,
      'separate_return_halt':RETURN,'transition_rows':len(table),'tests':count,'max_steps':max_steps,
      'table_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'states':IDS,
      'contract':'Consumes i units of a unary index counter; preserves entire arena except moving erased first-cell marker to record i; returns at marker+1.'}
    (Path(__file__).parent/'unary_locator_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
