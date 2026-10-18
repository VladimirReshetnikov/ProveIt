#!/usr/bin/env python3
"""Independent audit of the exact Detour242 relative machine proof.

This implementation does not import the construction or local-detour checker.
It checks a one-old-step to one/three-new-step relation with control map 27->15.
The global induction and converse-halting reasoning are in detour242_review.txt.
"""
from pathlib import Path
import argparse
import hashlib
import json

BASE_SHA='4207fc3d1bb16f3c64c3cff0980eaa1486160c3f467aee7685740a39e3df7300'
NEW_SHA='c8ef2f44d25fee6813164cc59ec05061799397da8cf7f0ea7baab63d32d76e02'
CANONICAL_SHA='ef8c07f372c76a73c021f51801f16f28f1e4ca5ead2d4ce6780c2a245a0db245'

def parse(path):
    raw=path.read_bytes();rows={};start=None
    for line in raw.decode('ascii').splitlines():
        if line.startswith('#! start '):
            assert start is None
            start=int(line.removeprefix('#! start '))
        elif line and not line.startswith('#'):
            tokens=line.split();assert len(tokens)==5
            state,bit,written,direction,target=tokens
            state,bit,written,target=map(int,(state,bit,written,target))
            assert state>=0 and target>=0 and bit in (0,1) and written in (0,1)
            assert direction in ('L','R') and (state,bit) not in rows
            rows[state,bit]=(written,{'L':-1,'R':1}[direction],target)
    assert start is not None
    states={s for s,b in rows}
    assert set(rows)=={(s,b) for s in states for b in (0,1)}
    return raw,start,rows,states


def controls(q):return 15 if q==27 else q

def symbolic_steps(rows,q,steps,initial):
    # Every unmentioned tape cell is a distinct opaque initial value.  A
    # branch inspecting one is rejected; untouched opaque cells survive.
    visited={};head=0;trace=[]
    for _ in range(steps):
        symbol=visited.get(head,initial.get(head,('opaque',head)))
        assert type(symbol) is int and symbol in (0,1)
        write,move,target=rows[q,symbol]
        trace.append([q,symbol,write,move,target,head])
        visited[head]=write
        head+=move;q=target
    normalized={i:v for i,v in visited.items() if v!=initial.get(i,('opaque',i))}
    return q,head,normalized,trace


def audit(root,out):
    baseline=root/'reference/zfc_combined243_old.tm'
    candidate=root/'machine/zfc_detour242_old.tm'
    canonical=root/'machine/zfc_detour242.tm'
    oldraw,oldstart,old,os=parse(baseline)
    newraw,newstart,new,ns=parse(candidate)
    canraw,canstart,can,cs=parse(canonical)
    shas=[hashlib.sha256(raw).hexdigest()for raw in(oldraw,newraw,canraw)]
    assert shas==[BASE_SHA,NEW_SHA,CANONICAL_SHA]
    assert (oldstart,newstart,canstart)==(95,95,0)
    assert len(os)==243 and len(old)==486 and len(ns)==242 and len(new)==484
    assert ns==os-{27} and cs==set(range(242))
    assert {t for w,d,t in old.values()}-os=={254}
    assert {t for w,d,t in new.values()}-ns=={254}
    assert {t for w,d,t in can.values()}-cs=={242}
    assert all(t!=27 for w,d,t in new.values())
    wanted={(q,b):(w,d,controls(t)) for(q,b),(w,d,t)in old.items()if q!=27}
    wanted[15,0]=(0,-1,32)
    assert new==wanted
    changed=[list(k)for k in sorted(new)if new[k]!=old[k]]
    assert changed==[[15,0],[18,0],[47,0],[65,0]]
    r=json.loads((root/'machine/renumbering.json').read_text())
    bij={int(k):v for k,v in r['old_to_canonical'].items()}
    assert set(bij)==ns|{254} and set(bij.values())==set(range(243))
    assert len(set(bij.values()))==243 and bij[95]==0 and bij[254]==242
    assert can=={(bij[q],b):(w,d,bij[t])for(q,b),(w,d,t)in new.items()}
    special={15,18,47,65}
    incoming={str(q):[[s,b,w,d]for(s,b),(w,d,t)in sorted(old.items())if t==q]
              for q in sorted(special|{27})}
    assert 95 not in special|{27}
    for q in special:
        assert incoming[str(q)]
        assert all(w==0 and d==1 for s,b,w,d in incoming[str(q)])
    assert incoming['27']==[[18,0,0,-1],[47,0,0,-1],[65,0,0,-1]]
    assert all(s in special for s,b,w,d in incoming['27'])
    # Ordinary mapped transition cases include the former 27/0 and the
    # incoming redirects.  Only 15/0 is a three-step case; 27/1 is unreachable.
    ordinary=0
    for (q,b)in sorted(old):
        if (q,b)in((15,0),(27,1)):continue
        oq,oh,ot,trace_old=symbolic_steps(old,q,1,{0:b})
        nq,nh,nt,trace_new=symbolic_steps(new,controls(q),1,{0:b})
        assert (controls(oq),oh,ot)==(nq,nh,nt)
        ordinary+=1
    assert ordinary==484
    oq,oh,ot,to=symbolic_steps(old,15,1,{-1:0,0:0})
    nq,nh,nt,tn=symbolic_steps(new,15,3,{-1:0,0:0})
    assert (oq,oh,ot)==(nq,nh,nt)==(21,1,{})
    assert [row[0] for row in tn]==[15,32,45]
    assert [row[4] for row in tn]==[32,45,21]
    assert all(row[4] in ns for row in tn)
    report={
      'status':'PASS_INDEPENDENT_RELATIVE_AUDIT',
      'baseline_sha256':shas[0],'candidate_old_sha256':shas[1],
      'candidate_canonical_sha256':shas[2],
      'working_states':242,'binary_rows':484,'canonical_start':0,'canonical_halt':242,
      'inherited_start':95,'inherited_halt':254,'deleted_inherited_state':27,
      'changed_retained_rows':changed,'renumbering_checked_for_all_rows':484,
      'complete_old_incoming_inventories':incoming,
      'mapped_one_step_cases':ordinary,'mapped_three_step_cases':1,
      'excluded_old_row_proved_unreachable':[27,1],
      'detour_old_trace':to,'detour_new_trace':tn,
      'detour_whole_tape_unchanged':True,
      'ordinary_theorem':'For every initial head and binary tape at shared state95, Combined243 and Detour242 have equivalent halting.',
      'clock':'At aligned old time n, new time tau(n)=n+2*A(n), where A counts old15/read0 steps before n; n<=tau(n)<=3*n.',
      'external_runtime_premise_required':False,
      'blank_reachability_screen_required':False,
      'proof_assistant_theorem_claimed':False,
      'independence':'New parser, literal comparison and symbolic-overlay executor; no import of the local-detour checker.',
      'scope':'Exact tables, static invariant, positive finite blocks, renumbering and ordinary two-way halting argument; inherited source-to-Con(ZFC) calibration and blank timing not independently replayed here.'}
    out.write_text(json.dumps(report,indent=2)+'\n')
    return report

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--package',type=Path,required=True,help='Root of the extracted zfc242-detour package')
    p.add_argument('--output',type=Path,default=Path(__file__).with_name('detour242_review.json'))
    a=p.parse_args();print(json.dumps(audit(a.package,a.output),indent=2))
