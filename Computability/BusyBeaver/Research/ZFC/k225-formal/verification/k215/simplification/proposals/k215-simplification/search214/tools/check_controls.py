#!/usr/bin/env python3
"""Positive and negative controls for the finite-window fold search."""
from pathlib import Path
import json,hashlib
from window_fold_search import parse,abstract,candidate_check
from indexed_fold_search import index_blocks

ROOT=Path(__file__).resolve().parents[1]

def check_closure(t,start,k,seen):
    """Independent tuple-based check of the bit-coded window fixed point."""
    assert seen[start]==set(range(1<<(2*k+1)))
    for q,words in seen.items():
        for bits in words:
            cells=[(bits>>i)&1 for i in range(2*k+1)]
            row=t.get((q,cells[k]))
            if row is None:continue
            w,d,z=row;cells[k]=w
            for outside in [0,1]:
                nxt=cells[1:]+[outside] if d==1 else [outside]+cells[:-1]
                value=sum(b<<i for i,b in enumerate(nxt))
                assert value in seen[z]

def main():
    reports=[]
    for pin in json.loads((ROOT/'input_pins.json').read_text()):
        p=ROOT/pin['file'];raw=p.read_bytes()
        assert len(raw)==pin['size']
        assert hashlib.sha256(raw).hexdigest()==pin['sha256']
        assert hashlib.sha1(f'blob {len(raw)}\0'.encode()+raw).hexdigest()==pin['git_blob_sha']
        start,t=parse(p)
        qs={q for q,b in t}
        assert len(qs)==215 and len(t)==430
        assert {(q,b)for q in qs for b in[0,1]}==set(t)
        assert {z for w,d,z in t.values()}-qs=={254}
        windows,n=abstract(t,start,4);check_closure(t,start,4,windows)
        reports.append({'input':pin['file'],'start':start,'abstract_states':n,'exact_input_and_window_closure':'PASS'})
    start,t=parse(ROOT/'inputs/primary.tm')
    # Explicitly unfold an accepted three-step predecessor-marker fold.
    u=dict(t)
    assert t[69,0]==(0,-1,213) and t[69,1]==(1,1,31)
    assert t[100,0]==(0,1,69) and t[53,1]==(1,1,69)
    assert t[213,0]==(0,1,92) and t[213,1]==(1,1,90)
    assert t[92,0]==(0,1,104) and t[90,0]==(0,1,105)
    u[69,0]=(0,1,105)
    u[400,0]=(0,1,104);u[400,1]=u[69,1]
    u[100,0]=(0,1,400)
    windows,n=abstract(u,start,3);check_closure(u,start,3,windows)
    positive=candidate_check(u,windows,3,69,400,0,0,-1,213,24)
    assert positive=={'cases':16,'max_duration':3,'min_duration':3}
    early_halt=candidate_check(u,windows,3,69,400,0,0,1,254,24)
    wrong_selector=candidate_check(u,windows,3,69,400,0,0,-1,201,24)
    assert early_halt is None and wrong_selector is None
    # Verify the indexed blocks independently agree on the positive control.
    actions,index=index_blocks(u,sorted({q for q,b in u}),3,24)
    aid=actions.index((0,-1,213));count=0
    for oldq in[69,400]:
        for bits in windows[oldq]:
            if(bits>>3)&1:continue
            w,d,z=u[oldq,0]
            hits=[(n,inside)for a,n,inside in index[(bits,w,d,z)] if a==aid and not({69,400}&inside)]
            assert hits and min(n for n,_ in hits)==3
            count+=1
    assert count==16
    # Identical contexts may legitimately match different old endpoints at
    # different positive times along the very same new trajectory.
    toy={}
    for bit in[0,1]:
        toy[1,bit]=(bit,1,4);toy[2,bit]=(bit,1,5)
        toy[4,bit]=(bit,-1,6);toy[6,bit]=(bit,1,5)
        toy[5,bit]=(bit,1,5)
    acts,ix=index_blocks(toy,[1,2,4,5,6],1,3)
    overlap=[]
    for bits in range(8):
        bit=(bits>>1)&1;aid=acts.index((bit,1,4))
        for target,steps in[(4,1),(5,3)]:
            matches=[n for a,n,inside in ix[(bits,bit,1,target)]if a==aid and not({1,2}&inside)]
            assert min(matches)==steps
            overlap.append((bits,target,steps))
    return {'status':'PASS','inputs':reports,'positive_fold69_400':positive,'indexed_positive_cases':count,'early_halt_rejected':True,'wrong_selector_rejected':True,'overlapping_context_distinct_endpoints_cases':len(overlap),'overlapping_context_durations':[1,3],'scope':'Finite implementation controls and independently checked abstract closure; no proof-assistant compilation and no general optimality claim.'}

if __name__=='__main__':
    r=main();(ROOT/'evidence/controls.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
