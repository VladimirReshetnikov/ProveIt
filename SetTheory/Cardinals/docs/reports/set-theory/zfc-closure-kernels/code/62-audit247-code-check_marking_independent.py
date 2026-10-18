#!/usr/bin/env python3
"""Check the literal premises of the universal selector-fold induction.

The finite regressions are supplemental. The quantified proof follows from
these selector-loop rows, the common action on known input 1, and induction
on unary blocks; see sections/reduction_and_calibration.tex.
Uses only the Python standard library.
"""
from pathlib import Path
import argparse,hashlib,json,random

def parse(p):
    t={}
    for line in p.read_text().splitlines():
        if not line or line.startswith('#'):continue
        q,b,w,d,n=line.split();q,b,w,n=map(int,(q,b,w,n))
        assert (q,b) not in t and d in ('L','R')
        t[q,b]=(w,1 if d=='R' else -1,n)
    return t

def run_mark(t,selector,v,r,left):
    bits=[]
    for x in v:bits.extend([0]+[1]*(x+1))
    ones=left|{i for i,b in enumerate(bits)if b}
    target=ones-{sum(x+2 for x in v[:r])+1}
    q=selector;h=0;steps=0
    while True:
        if steps and h==-1 and q==(2 if r==0 else 6):
            assert ones==target
            return steps
        assert h>=0 and steps<100000
        w,d,q=t[q,int(h in ones)]
        if w:ones.add(h)
        else:ones.discard(h)
        h+=d;steps+=1

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--baseline',type=Path,required=True);ap.add_argument('--candidate',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
    if not __debug__:raise RuntimeError('Assertions are part of the audit; do not use -O.')
    old,new=parse(a.baseline),parse(a.candidate);deleted={0,1,3}
    expected={k:v for k,v in old.items()if k[0]not in deleted};expected[60,0]=(0,1,20)
    assert new==expected and len(new)==494
    states={q for q,b in new};assert all(t in states|{254}for w,d,t in new.values())
    s=[60,44,31,56,38,40,28,64,69];rows=[]
    for r,q in enumerate(s):
        assert old[q,1]==new[q,1]==(1,1,q)
        assert old[q,0]==(0,1,0 if r==0 else s[r-1])
        assert new[q,0]==(0,1,20 if r==0 else s[r-1])
        rows.append({'register':r,'state':q,'read_one':old[q,1],'old_read_zero':old[q,0],'new_read_zero':new[q,0]})
    assert old[0,1]==old[20,1]==new[20,1]==(0,-1,2)
    into=lambda t,x:sorted([list(k)for k,v in t.items()if v[2]==x])
    assert into(old,0)==[[60,0]]
    assert into(old,1)==[[0,0],[1,1],[3,1]]
    assert into(old,3)==[[1,0]]
    assert all(v[2]not in deleted for v in new.values())
    samples=0;steps=0
    for r in range(9):
        for seed in range(25):
            v=[(7*i+seed)%8 for i in range(10+seed%5)]
            n=run_mark(old,s[r],v,r,{-1,-3,-5});m=run_mark(new,s[r],v,r,{-1,-3,-5})
            assert n==m;samples+=1;steps+=n+m
    data={'status':'PASS','proof_scope':'Literal finite premises for the arbitrary-value selector induction, plus supplemental finite regressions; not a proof-assistant kernel result.','baseline_sha256':hashlib.sha256(a.baseline.read_bytes()).hexdigest(),'candidate_sha256':hashlib.sha256(a.candidate.read_bytes()).hexdigest(),'states':247,'rows':494,'exact_removed_states':sorted(deleted),'only_changed_surviving_row':{'state':60,'read':0,'before':[0,'R',0],'after':[0,'R',20]},'selector_rows':rows,'shared_action':{'old_state':0,'new_state':20,'read':1,'action':[0,'L',2]},'incoming_edges_to_deleted_states':{str(q):into(old,q)for q in sorted(deleted)},'regressions':{'cases':samples,'literal_steps_both_machines':steps,'all_complete_tapes_and_step_counts_equal':True}}
    a.output.write_text(json.dumps(data,indent=2)+'\n');print(json.dumps({k:v for k,v in data.items()if k not in ('selector_rows','incoming_edges_to_deleted_states')},indent=2))
if __name__=='__main__':main()
