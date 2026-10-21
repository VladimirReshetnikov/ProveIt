#!/usr/bin/env python3
"""Literal 44-step counterexample to the rejected CB1 shortcut.

Usage: python check_rejected_shortcut.py OLD_NATIVE_TM [CORRECTED_NATIVE_TM]

This isolates one valid primitive frame. It is not a blank-run assertion.
Both tables are parsed independently; no runtime-checker modules are used.
"""
import hashlib
import json
import sys
from pathlib import Path

OLD_SHA='289737cb4729000f9a68fa1a55a947189e9bfa1e833998590d168036c0c85598'
NEW_SHA='03739f080d023166773bc14e7e3a4d8157f81d44c28cd30fef46066b37cf3748'

def table(path):
    out={}
    for line in Path(path).read_text().splitlines():
        if not line or line.startswith('#'):continue
        q,b,w,d,n=line.split();q,b,w,n=map(int,(q,b,w,n))
        assert (q,b) not in out and b in (0,1) and w in (0,1) and d in ('L','R')
        out[q,b]=(w,1 if d=='R' else -1,n)
    return out

def zero_frame(pc):
    # Marker -1; padded 64-bit address; header 64; nine zero registers and
    # one zero spare, each encoded by B(0)=01.
    return {-1,64}|{i for i,b in enumerate(pc) if b=='1'}|set(range(66,85,2))

def complete_dispatch(q,head,ones):
    if q!=84:return False
    aligned={x-head for x in ones}
    if -1 not in aligned or any(x < -1 for x in aligned):return False
    right=sorted(x for x in aligned if x>=52)
    if not right or right[0]<64:return False
    p=right[0]+1;last=max(aligned);values=[]
    while p<last and p not in aligned and p+1 in aligned:
        start=p+1;p=start
        while p in aligned:p+=1
        values.append(p-start-1)
    return p==last+1 and len(values)>=10

def run(path):
    t=table(path);ones=zero_frame('11010011');q=84;head=0
    for tick in range(1,100001):
        write,move,q=t[q,int(head in ones)]
        if write:ones.add(head)
        else:ones.discard(head)
        head+=move
        if complete_dispatch(q,head,ones):
            return {'steps':tick,'state':q,'head':head,'one_cells':sorted(ones),
                    'control_one_offsets':sorted(x-head for x in ones if 0<=x-head<64)}
    raise AssertionError('No complete dispatcher return within finite check limit')

if __name__=='__main__':
    old=Path(sys.argv[1]);assert hashlib.sha256(old.read_bytes()).hexdigest()==OLD_SHA
    actual=run(old);expected=sorted(zero_frame('11011'))
    assert actual['steps']==44 and actual['state']==84 and actual['head']==0
    assert actual['control_one_offsets']==[0,1,2,6]
    assert actual['one_cells']!=expected
    out={'status':'CONCRETE_REJECTED_SHORTCUT_COUNTEREXAMPLE',
         'old_table_sha256':OLD_SHA,'source_ordinal':4697,
         'site':['11010011','CB',1],
         'initial_registers':[0]*9,'initial_spares':[0],'initial_gap':0,
         'initial_one_cells':sorted(zero_frame('11010011')),
         'expected_successor':'11011','expected_one_cells':expected,
         'rejected_table_actual':actual,
         'scope':'Exact finite primitive-frame mismatch, not a claim about the rejected table on blank tape.'}
    if len(sys.argv)>2:
        repaired=Path(sys.argv[2]);assert hashlib.sha256(repaired.read_bytes()).hexdigest()==NEW_SHA
        good=run(repaired)
        assert good['state']==84 and good['head']==0 and good['one_cells']==expected
        out['corrected_table_sha256']=NEW_SHA
        out['corrected_table_actual']=good
        out['corrected_primitive_status']='PASS_THIS_CONCRETE_FRAME'
    print(json.dumps(out,indent=2))
