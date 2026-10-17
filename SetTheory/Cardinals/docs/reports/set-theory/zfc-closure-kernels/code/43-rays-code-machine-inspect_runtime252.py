#!/usr/bin/env python3
"""Inspect sound-entry candidates in the known old5->64 252-state runtime.

This is a literal bounded simulation, not a proof of consistency equivalence.
It accepts every root-phase register frame; no exact public bootstrap matching.
"""
from pathlib import Path
import argparse, collections, importlib.util, json, re, time

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('m253gen', HERE/'upstream/ZF/m253/tools/generate_candidate.py')
gen = importlib.util.module_from_spec(spec); spec.loader.exec_module(gen)
_program_source=(HERE/'upstream/ZF/m254/coq/tm/Prog254.v').read_text()
_program_body=_program_source.split('Definition p254_tab : list (cedge * cedge) := [',1)[1].split('].',1)[0]
PROGRAM=[]
for aa,bb in re.findall(r'\(([^,]+), ([^)]+)\)',_program_body):
    def edge(s):
        bits=s.strip().split();return bits[0],int(bits[1]) if len(bits)>1 else 0
    PROGRAM.append((edge(aa),edge(bb)))
assert len(PROGRAM)==6459

def load_runtime():
    base = gen.patched_rows()
    rows = {(q,b): (w, 1 if d == 'R' else -1, 64 if n == 5 else n)
            for (q,b),(w,d,n) in base.items() if q != 5}
    assert len(rows)==504
    return rows

def frame(ones, head, minimum_gap=40, allow_pc=False):
    """Decode a literal prefix-tree site and require all following padding zero."""
    if head-1 not in ones or min(ones) != head-1:
        return None
    pc=[];site=None
    if allow_pc:
        node=0
        while True:
            b=int(head+len(pc) in ones);pc.append(b)
            tag,arg=PROGRAM[node][b]
            if tag!='CN':site=[tag,arg];break
            node=arg
            assert len(pc)<35
    right = sorted(x for x in ones if x >= head+len(pc))
    if not right:
        return None
    header=right[0]; gap=header-head
    if gap<minimum_gap or len(right)<10 or right[1] != header+2:
        return None
    runs=[]; start=prev=right[1]
    for x in right[2:]:
        if x==prev+1:
            prev=x; continue
        if x!=prev+2:
            return None
        runs.append(prev-start); start=prev=x
    runs.append(prev-start)
    if len(runs)<9:
        return None
    # physical: ws,p1,ac,s2,s1,pl,np,tw,p2
    ws,p1,ac,s2,s1,pl,np,tw,p2=runs[:9]
    return dict(gap=gap,pc=''.join(map(str,pc)),site=site,physical=runs[:9], spares=len(runs)-9,
                all_theorem_slots_zero=(ws==tw==p2==0),
                scratch_zero=(ac==s1==s2==0),
                first_nine_and_higher_register_data=runs,
                nextproof=np, prooflist=pl, param1=p1)

def simulate(start,limit,retain=100):
    rows=load_runtime(); ones=set(); head=0; q=start
    visits=roots=0; found=[]; good=[]; first_dispatch=[]; minroots=[];general=[]
    general_gaps=collections.Counter(); full_frames=0; endpoint=None;last_generic=collections.deque(maxlen=12)
    record_gaps=[];max_gap=-1
    gaps=collections.Counter(); bad_left=0
    begin=time.monotonic()
    for step in range(limit+1):
        if q==96:
            visits+=1
            if ones and min(ones)==head-1:
                right=[x for x in ones if x>=head]
                if right:gaps[min(right)-head]+=1
            else:bad_left+=1
            if len(first_dispatch)<6:
                first_dispatch.append(dict(step=step,head=head,ones=sorted(ones)))
            f=frame(ones,head)
            if f:
                roots+=1; f.update(step=step,head=head)
                if len(found)<retain: found.append(f)
                if f['all_theorem_slots_zero'] and f['scratch_zero']:
                    good.append(f); break
            elif len(minroots)<20:
                f=frame(ones,head,minimum_gap=0)
                if f:
                    f.update(step=step,head=head);minroots.append(f)
            gf=frame(ones,head,minimum_gap=0,allow_pc=True)
            if gf:
                general_gaps[gf['gap']]+=1
                if gf['gap']>max_gap:
                    max_gap=gf['gap'];record=dict(gf);record.update(step=step,head=head,ones=sorted(ones));record_gaps.append(record)
                small={k:v for k,v in gf.items() if k!='first_nine_and_higher_register_data'}
                small.update(step=step,head=head);last_generic.append(small)
                if len(general)<20 or (gf['gap']>=40 and full_frames<20):
                    gf.update(step=step,head=head);general.append(gf)
                if gf['gap']>=40:
                    full_frames+=1
                    if endpoint is None:
                        endpoint=dict(gf);endpoint.update(step=step,head=head,ones=sorted(ones))
        if step==limit or q==254: break
        w,d,q=rows[q,int(head in ones)]
        if w: ones.add(head)
        else: ones.discard(head)
        head+=d
    return dict(start=start,limit=limit,steps=step,state=q,head=head,ones=len(ones),
                dispatch_visits=visits,root_frames=roots,root_samples=found,sound_zero_seeds=good,
                first_dispatch=first_dispatch,underlength_root_samples=minroots,
                generic_frames=general,generic_gap_histogram=dict(general_gaps),
                final_generic_frames=list(last_generic),
                record_gap_frames=record_gaps,
                full_generic_frames=full_frames,first_full_generic_frame=endpoint,
                first_one_gap_histogram=dict(gaps),bad_left_boundary=bad_left,
                final_first_100_ones=sorted(ones)[:100],final_all_ones=sorted(ones),elapsed=time.monotonic()-begin)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--start',type=int,default=64)
    p.add_argument('--limit',type=int,default=10000000);p.add_argument('--output',type=Path)
    a=p.parse_args();r=simulate(a.start,a.limit)
    if a.output:a.output.write_text(json.dumps(r,indent=2)+'\n')
    print(json.dumps({k:v for k,v in r.items() if k not in ('first_dispatch','root_samples','underlength_root_samples','generic_frames','final_first_100_ones','final_all_ones','final_generic_frames','record_gap_frames')},indent=2))
