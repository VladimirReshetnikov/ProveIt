#!/usr/bin/env python3
"""Bounded independent table check of composing the latest MS rule with ours.

This is a local compatibility/state-accounting review, not an additional
delivered calibrated machine or a search for arbitrary state reductions.
"""
import argparse
import hashlib
import json
from pathlib import Path


def read(p):
    rows={}
    for line in p.read_text().splitlines():
        q,b,w,d,t=line.split()
        q,b,w,t=map(int,(q,b,w,t))
        assert d in ('L','R') and (q,b) not in rows
        rows[q,b]=(w,1 if d=='R' else -1,t)
    assert len(rows)==388
    return rows


def rename(q):return 400 if q==51 else 88 if q==301 else q


def review(path):
    old=read(path);controls={q for q,b in old}
    assert len(controls)==194 and 400 not in controls
    expected={(51,0):(0,1,16),(51,1):(1,1,51),
              (301,0):(0,1,45),(301,1):(1,1,103),
              (88,0):(0,1,122),(88,1):(1,1,103)}
    assert all(old[k]==v for k,v in expected.items())
    new={(rename(q),b):(w,d,rename(t)) for(q,b),(w,d,t)in old.items() if q!=301}
    new[88,0]=(0,-1,51)
    new[51,0]=(0,1,122);new[51,1]=(1,1,51)
    incoming={q:[(s,b,w,d)for(s,b),(w,d,t)in old.items()if t==q]for q in(301,88)}
    for q,h in((301,0),(88,1)):
        assert incoming[q] and {(w,d)for s,b,w,d in incoming[q]}=={(h,1)}
    ordinary=[k for k in old if k[0] not in(301,88)]
    for q,b in ordinary:
        w,d,t=old[q,b];assert new[rename(q),b]==(w,d,rename(t))
    durations=[]
    for q,h in((301,0),(88,1)):
        for b in(0,1):
            w,d,t=old[q,b];goal=(rename(t),d,{-1:h,0:w})
            state,pos,tape=88,0,{-1:h,0:b}
            for steps in range(1,6):
                assert pos in(-1,0)
                wr,move,state=new[state,tape[pos]]
                tape[pos]=wr;pos+=move
                if(state,pos,tape)==goal:break
            else:raise AssertionError(('local trace',q,b))
            durations.append(steps)
    assert durations==[5,1,3,1]
    controls={q for q,b in new};assert len(controls)==194 and len(new)==388
    order=[74];seen={74}
    for q in order:
        for b in(0,1):
            t=new[q,b][2]
            if t!=254 and t not in seen:seen.add(t);order.append(t)
    assert seen==controls
    # Exact deterministic-action congruence, with terminal write/move ignored.
    classes={q:0 for q in controls};classes[254]=1
    while True:
        kinds={};next_classes={254:-1}
        for q in sorted(controls):
            signature=[]
            for b in(0,1):
                w,d,t=new[q,b]
                signature.append(('H',)if t==254 else(w,d,classes[t]))
            signature=tuple(signature)
            if signature not in kinds:kinds[signature]=len(kinds)
            next_classes[q]=kinds[signature]
        same=all((classes[a]==classes[b])==(next_classes[a]==next_classes[b])
                 for a in controls for b in controls)
        classes=next_classes
        if same:break
    count=len({classes[q]for q in controls})
    assert count==194
    return {'source_native_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
            'status':'PASS','old_controls':194,'new_controls':194,
            'rows':388,'ordinary_rows_checked':len(ordinary),'local_durations':durations,
            'incoming_edges':incoming,'all_controls_graph_reachable':True,
            'deterministic_action_congruence_classes':count,
            'conclusion':'The new marker split/merge composes locally, but gives no state saving and no exact deterministic-action quotient saving.'}


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--mp',type=Path,required=True)
    ap.add_argument('--lcsf3',type=Path,required=True)
    ap.add_argument('--output',type=Path,required=True)
    a=ap.parse_args()
    r={'status':'PASS','scope':'Bounded local compatibility and exact action-congruence check. No universal lower bound and no new advertised calibrated machine.',
       'MP_plus_MS':review(a.mp),'LCSF3_plus_MS':review(a.lcsf3)}
    a.output.parent.mkdir(parents=True,exist_ok=True)
    a.output.write_text(json.dumps(r,indent=2)+'\n')
    print(json.dumps(r,indent=2))


if __name__=='__main__':main()
