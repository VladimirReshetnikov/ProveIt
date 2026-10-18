#!/usr/bin/env python3
"""Literal full-tape witness that threshold74's failing leaf is reached."""
from pathlib import Path
import sys,json,time,hashlib
from collections import Counter
from program import B,lookup,bad_leaves
sys.path.insert(0,str(B/'code'))
import check_literal_instructions as lit

ROOT=Path(__file__).resolve().parent
T=lit.read_table(B/'machine/zfc_prefix246_old.tm')
U=T.copy();U[58,0]=(0,-1,84)

def one_step(table,q,h,one):
    w,delta,q=table[q,int(h in one)]
    if w:one.add(h)
    else:one.discard(h)
    return q,h+delta

def clean_frame(q,h,one):
    if q!=96 or not one or min(one)!=h-1:return None
    headers=[x for x in one if x>=h+34]
    if not headers:return None
    header=min(headers)
    if header-h<40:return None
    pc=''.join('1' if h+i in one else '0' for i in range(34)).rstrip('0')
    p,op,r,_,_=lookup(pc)
    if any(h+i in one for i in range(len(p),header-h)):return None
    vals=[];pos=header+1;end=max(one)
    while pos<=end:
        if pos in one or pos+1 not in one:return None
        start=pos+1;pos=start
        while pos in one:pos+=1
        vals.append(pos-start-1)
    if len(vals)<10:return None
    if lit.paint(pc,header-h,vals[:9],vals[9:],h)!=one:return None
    return dict(head=h,header_distance=header-h,pc=pc,
                physical_registers=vals[:9],spares=vals[9:])

def main():
    bad=bad_leaves()
    began=time.monotonic();q,h,one=95,0,set();total=0
    for _ in range(410735):q,h=one_step(T,q,h,one)
    total=410735
    R=[0,0,0,3,0,0,3,0,0];S=[1]*167;pc='';span=181
    assert (q,h)==(96,-5) and one==lit.paint(pc,span,R,S,h)
    counts=Counter();instruction_lengths=[]
    for index in range(2000):
        p,op,r,_,_=lookup(pc)
        if p in bad:break
        target=lit.expected(p,op,r,R,S,h,span)
        assert target is not None
        steps=0
        while True:
            q,h=one_step(T,q,h,one);steps+=1;total+=1
            assert q!=254 and steps<1000000
            if q==96 and h==target[0] and one==target[1]:break
        h,_,pc,span,R,S=target
        counts[op]+=1;instruction_lengths.append(steps)
        if index%250==249:print('verified_source_instructions',index+1,'binary_time',total,flush=True)
    else:raise AssertionError('No bad leaf in requested prefix')
    assert index==1700 and p=='111010010010000000'
    before=dict(state=q,head=h,header_distance=span,pc=pc,consumed_leaf=p,
                physical_registers=R.copy(),spares=S.copy(),all_one_positions=sorted(one))
    target=lit.expected(p,op,r,R,S,h,span)
    assert target is not None
    variants={}
    for name,table in [('baseline246',T),('threshold245_runtime',U)]:
        vq,vh,vo=q,h,one.copy();first_frame=None;reached_target=None
        trace=[]
        for steps in range(1,200001):
            source=(vq,int(vh in vo))
            vq,vh=one_step(table,vq,vh,vo)
            if source==(58,0):trace.append(dict(time=steps,source=[58,0],head_after=vh,state_after=vq))
            if vq==254:break
            if vq==96 and vh==target[0] and vo==target[1]:
                reached_target=steps
                if first_frame is None:first_frame=dict(time=steps,frame=clean_frame(vq,vh,vo))
                break
            frame=clean_frame(vq,vh,vo)
            if frame is not None and first_frame is None:
                first_frame=dict(time=steps,frame=frame)
                if name!='baseline246':break
        variants[name]=dict(steps=steps,state=vq,head=vh,reached_expected_target=reached_target,
                            first_clean_frame=first_frame,threshold_visits=trace[:20],
                            all_one_positions=sorted(vo),status='HALT' if vq==254 else 'ACTIVE')
    expected=dict(head=target[0],pc=target[2],header_distance=target[3],
                  physical_registers=target[4],spares=target[5])
    # Check the possible alternate explanation that the mutant merely contracts
    # several harmless original source steps. At its first target PC the
    # original program has changed the actual theorem stack.
    mutant_frame=variants['threshold245_runtime']['first_clean_frame']['frame']
    sr,ss,spc,sh,sd=R.copy(),S.copy(),pc,h,span
    source_skip=None
    for skipped in range(20000):
        if skipped and spc.rstrip('0')==mutant_frame['pc'].rstrip('0'):
            source_skip=dict(source_steps=skipped,head=sh,header_distance=sd,
                pc=spc,physical_registers=sr,spare_count=len(ss),
                same_primary_registers=(sr==mutant_frame['physical_registers']))
            break
        pp,oo,rr,_,_=lookup(spc)
        nxt=lit.expected(pp,oo,rr,sr,ss,sh,sd)
        assert nxt is not None
        sh,_,spc,sd,sr,ss=nxt
    assert source_skip is not None and source_skip['source_steps']==146
    assert source_skip['physical_registers'][0]==10
    out=dict(status='PASS',scope='Finite literal reachability and differing next clean frame; no global inconsistency claim.',
             instructions_before_failure=index,absolute_binary_time=total,
             instruction_counts=dict(counts),instruction_lengths=instruction_lengths,
             reached_frame=before,expected_target=expected,variants=variants,
             original_source_at_mutant_pc=source_skip,
             seconds=time.monotonic()-began)
    (ROOT.parent/'results/threshold-literal-witness.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ('instruction_lengths','reached_frame','expected_target','variants')},indent=2))
    print('frame', {k:v for k,v in before.items() if k not in ('spares','all_one_positions')},'spares',len(S))
    for name,v in variants.items():
        print(name,{k:w for k,w in v.items() if k not in ('all_one_positions','first_clean_frame')})
        f=v['first_clean_frame']
        if f is not None:
            print('first_clean_frame',f['time'],{k:w for k,w in f['frame'].items() if k!='spares'},'spares',len(f['frame']['spares']))

if __name__=='__main__':main()
