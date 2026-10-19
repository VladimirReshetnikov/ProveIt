#!/usr/bin/env python3
"""Classify every blank start and search exact complete safe-root frames.

The classification before the first 1-write is exact modulo tape translation.
Bounded run failure is reported as bounded only. A passing root includes every
one-coordinate and is rechecked by a separately implemented dense interpreter.
"""
from pathlib import Path
from collections import defaultdict
import argparse, hashlib, json, time

PHYSICAL=(6,2,0,4,3,7,8,5,1)

def read_table(path):
    table={}
    for line in path.read_text().splitlines():
        if not line or line.startswith('#'):continue
        q,b,w,d,t=line.split(); q,b,w,t=map(int,(q,b,w,t))
        assert b in (0,1) and w in(0,1) and d in('L','R') and (q,b) not in table
        table[q,b]=w,1 if d=='R' else-1,t
    states={q for q,b in table}; assert len(table)==2*len(states)
    return table,states

def classify(table,states):
    classes=defaultdict(list); silent=[]; halt=[]
    for initial in sorted(states):
        q=initial;h=0;steps=0;seen={}
        while q not in seen and q in states:
            seen[q]=(steps,h);w,d,t=table[q,0]
            if w:
                classes[q].append(dict(initial=initial,prefix_steps=steps,prefix_head=h));break
            steps+=1;h+=d;q=t
        else:
            if q not in states:halt.append(dict(initial=initial,steps=steps,head=h,state=q))
            else:
                prior,ph=seen[q]
                silent.append(dict(initial=initial,entry_steps=prior,period_steps=steps-prior,period_displacement=h-ph,loop_state=q))
    return classes,silent,halt

def frame(ones,head,padding,allow_nonempty=False):
    if not ones or min(ones)!=head-1:return None
    right=sorted(p for p in ones if p>=head)
    if not right:return None
    header=right[0]
    if header-head<padding:return None
    # This branch accepts exactly an empty program pointer and a complete
    # 1-header, nine B(v) register words and a nonempty spare suffix.
    values=[];p=header+1;end=right[-1]
    while p<=end:
        if p in ones or p+1 not in ones:return None
        p+=1;start=p
        while p in ones:p+=1
        values.append(p-start-1)
    if len(values)<10:return None
    logical=[values[i] for i in PHYSICAL]
    if any(logical[i] for i in(1,2,5)):return None
    return dict(head=head,marker=head-1,header=header,header_distance=header-head,
        logical_registers=logical,physical_registers=values[:9],spare_values=values[9:],
        pc='',all_one_positions=sorted(ones),one_count=len(ones),all_other_cells_zero=True)

def run(table,states,initial,dispatcher,limit,padding):
    q=initial;h=0;ones=set();low=0;high=0
    for tick in range(limit+1):
        if q==dispatcher:
            candidate=frame(ones,h,padding)
            if candidate:return dict(status='PASS',start=initial,dispatcher=dispatcher,steps=tick,**candidate)
        if q not in states:return dict(status='HALTED',start=initial,steps=tick,head=h,state=q)
        if tick==limit:break
        w,d,t=table[q,int(h in ones)]
        # Exact simple escape proof: this self-loop heads out into a wholly
        # blank half-line, writes behind the head, and remains in the state.
        if t==q and ((d==1 and (not ones or h>high)) or (d==-1 and(not ones or h<low))):
            return dict(status='PROVED_OUTWARD_SELF_LOOP',start=initial,steps=tick,state=q,head=h,write=w,direction=d)
        if w:
            ones.add(h);low=min(low,h);high=max(high,h)
        else:ones.discard(h)
        h+=d;q=t
    return dict(status='NO_FRAME_WITHIN_BOUND',start=initial,bound=limit,state=q,head=h,one_count=len(ones))

def dense_verify(table,result):
    n=result['steps'];offset=n+1;cells=bytearray(2*n+3);h=offset;q=result['start']
    for tick in range(n):
        w,d,q=table[q,cells[h]];cells[h]=w;h+=d
    assert q==result['dispatcher'] and h-offset==result['head']
    assert [i-offset for i,b in enumerate(cells) if b]==result['all_one_positions']

def main():
    ap=argparse.ArgumentParser();ap.add_argument('table',type=Path);ap.add_argument('--output',type=Path,required=True);ap.add_argument('--limit',type=int,default=2000000);ap.add_argument('--padding',type=int,default=64);ap.add_argument('--dispatcher',type=int,default=96);args=ap.parse_args()
    assert __debug__ and args.limit>=0 and args.padding>=0
    table,states=read_table(args.table);classes,silent,halt=classify(table,states);began=time.monotonic();results=[]
    for writer in sorted(classes):
        result=run(table,states,writer,args.dispatcher,args.limit,args.padding)
        if result['status']=='PASS':dense_verify(table,result);result['independent_dense_replay']=True
        results.append(result)
        print(writer,result['status'],result.get('steps',result.get('bound')),flush=True)
    obj=dict(status='COMPLETE_START_CLASSIFICATION',table_sha256=hashlib.sha256(args.table.read_bytes()).hexdigest(),working_states=len(states),first_write_classes={str(k):v for k,v in classes.items()},silent_zero_cycles=silent,silent_halts=halt,run_results=results,seconds=time.monotonic()-began,
        scope='All initial states are classified modulo translation before first 1-write; a bounded failure of a writer class is not a nonhalting proof.')
    args.output.write_text(json.dumps(obj,indent=2)+'\n')
if __name__=='__main__':main()
