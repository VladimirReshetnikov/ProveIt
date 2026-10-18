#!/usr/bin/env python3
"""Locate threshold74 failure leaves in exact source-register executions."""
from pathlib import Path
from collections import deque
import sys, json, time

ROOT=Path(__file__).resolve().parents[1]
B=ROOT/'reference/context246'
sys.path.insert(0,str(B/'code'))
import review_affine_source as audit

nodes,sites=audit.parse_source(B/'sources/Prog254.v')
physical_to_logical={p:i for i,p in enumerate(audit.PHYSICAL)}

def bad_leaves():
    """Load the separate threshold experiment only when it is requested."""
    failures=json.loads((ROOT/'data/threshold-failures.json').read_text())
    return {x['pc'] for x in failures}

def build_site(p,op,physical):
    r=physical_to_logical[physical] if op in ('CD','CI') else physical
    inc=audit.full_inc(p)[0].rstrip('0')
    if op=='CI': return p,op,r,inc,inc
    if op=='CD': return p,op,r,inc,audit.full_inc(audit.full_strip(p,'0',1))[0].rstrip('0')
    if op=='CB':
        nxt=audit.full_inc(audit.full_strip(p,'0',r))[0].rstrip('0')
        return p,op,r,nxt,nxt
    if op=='CC':
        nxt=audit.full_strip(p,'1',r).rstrip('0')
        return p,op,r,nxt,nxt
    return p,op,r,None,None

site_map={p:build_site(p,op,physical) for p,op,physical in sites}
lookup_cache={}
def lookup(pc):
    if pc in lookup_cache:return lookup_cache[pc]
    n,i,p=0,0,''
    while True:
        b=int(pc[i]) if i<len(pc) else 0
        p+=str(b);i+=1
        op,arg=nodes[n][b]
        if op!='CN':
            answer=site_map[p]
            lookup_cache[pc]=answer
            return answer
        n=arg

def walk(registers,limit=1000000,stop_first=True):
    # This data is needed only by the obstruction search, not by users of the
    # frozen source graph (including the inductive-invariant checkers).
    bad=bad_leaves()
    initial=registers.copy();R=registers.copy();pc='';recent=deque(maxlen=30)
    found=[];started=time.monotonic()
    for step in range(limit):
        p,op,r,pos,zero=lookup(pc)
        record=dict(step=step,stored_pc=pc,leaf=p,operation=op,logical_argument=r,registers=R.copy())
        if p in bad:
            record['branch_zero']=R[r]==0
            record['physical_registers']=[R[i] for i in (2,8,1,4,3,7,0,5,6)]
            record['initial_logical_registers']=initial
            record['previous']=list(recent)
            found.append(record)
            if stop_first:break
        recent.append(record)
        if op=='CI':R[r]+=1;pc=pos
        elif op=='CD':
            if R[r]:R[r]-=1;pc=pos
            else:pc=zero
        elif op=='CH':
            return dict(status='HALT',steps=step,initial=initial,found=found,seconds=time.monotonic()-started)
        else:pc=pos
    return dict(status='FOUND' if found else 'CUTOFF',steps=step,initial=initial,
                final_registers=R,pc=pc,found=found,seconds=time.monotonic()-started)

if __name__=='__main__':
    starts=[[3,0,0,0,3,0,0,0,0],[0]*9,[1,0,0,0,4,0,0,0,2],
            [2,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,3],
            [3,0,0,0,0,0,0,0,0]]
    out=[]
    for R in starts:
        result=walk(R,1000000)
        out.append(result)
        print(json.dumps({k:v for k,v in result.items() if k!='found'}),flush=True)
        if result['found']:
            print(json.dumps({k:v for k,v in result['found'][0].items() if k!='previous'}),flush=True)
    (ROOT/'results/threshold-reachable-frames.json').write_text(json.dumps(out,indent=2)+'\n')
