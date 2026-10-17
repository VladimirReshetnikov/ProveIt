#!/usr/bin/env python3
"""Exhaustive interval splitting for composed symbolic register excursions.

Search is bounded; every accepted contract must pass every nonempty interval
branch. We restart the whole trace after each split, never trust a stale
symbolic checkpoint, and distinguish diagnostic failures from impossibility.
"""
from pathlib import Path
import sys,json,time
from collections import Counter
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'binary_experiments'))
import common as c
import multieffect as me
BOUNDS=None
STATS=Counter()
class NeedSplit(Exception):
    def __init__(self,r,pivot):self.r,self.pivot=r,pivot
def bound_lookup(branch,r):return BOUNDS[r]
me.bounds=bound_lookup
def oracle(q,branch,state):
    try:return me.oracle(q,branch,state)
    except AssertionError as err:
        d=err.args[0] if err.args else None
        if isinstance(d,tuple)and d[0]=='undetermined sequential guard':
            r,delta=d[1],d[2]
            raise NeedSplit(r,-delta[r])
        raise
c.strict.oracle=oracle

def check(rows,i,split_budget=64):
    global BOUNDS
    p,op,r,z,branch,target=c.CASES[i]
    initial=[(0,None)]*9
    if branch is not None:initial[branch[0]]=(0,0)if branch[1]else(1,None)
    stack=[tuple(initial)];leaves=0;splits=0
    while stack:
        BOUNDS=stack.pop();STATS['trace_restarts']+=1
        try:
            _,lit=c.strict.run(rows,p,branch,target,halt=op=='CH',fuel=1000)
            assert lit>0
            leaves+=1
        except NeedSplit as request:
            if splits>=split_budget:return False,'split_budget',splits,leaves
            r,pivot=request.r,request.pivot;lo,hi=BOUNDS[r]
            assert pivot==lo and(hi is None or hi>pivot),(BOUNDS,r,pivot)
            zero=list(BOUNDS);positive=list(BOUNDS)
            zero[r]=(pivot,pivot);positive[r]=(pivot+1,hi)
            stack.extend([tuple(positive),tuple(zero)])
            splits+=1;STATS['exhaustive_splits']+=1
        except(AssertionError,KeyError)as err:
            return False,str(err),splits,leaves
    return True,None,splits,leaves

if __name__=='__main__':
    before=time.monotonic()
    # Baseline checks exercise every original source guard with arbitrary values.
    for i in range(len(c.CASES)):
        ok,err,_,_=check(c.T,i);assert ok,(i,err)
    previous=json.loads((ROOT/'binary_experiments/multieffect_fold_results.json').read_text())
    selected=[]
    for group in previous['groups']:
        for dst,i,reason in group['failures']:
            if 'undetermined sequential guard'in reason:selected.append((group['deleted'],dst,i))
    assert len(selected)==22923
    results=[];survivors=[];first_pass=0;counts=Counter()
    for k,(dead,dst,first_failure)in enumerate(selected):
        rows=c.fold(c.T,str(dead),str(dst))
        ok,err,splits,leaves=check(rows,first_failure)
        failed=first_failure
        if ok:
            first_pass+=1
            for i in range(len(c.CASES)):
                if i==first_failure:continue
                ok,err,ns,nl=check(rows,i);splits+=ns;leaves+=nl
                if not ok:failed=i;break
            else:
                failed=None;survivors.append([dead,dst])
                print('SURVIVOR',dead,dst,flush=True)
        counts[err if err is None else err.split(',')[0]]+=1
        results.append({'deleted':dead,'replacement':dst,'first_old_failure':first_failure,
                        'first_new_failure':failed,'reason':err,'splits':splits,'passed_branches':leaves})
        if k%1000==0:print('progress',k,len(selected),round(time.monotonic()-before,2),flush=True)
    out={'baseline_cases':8391,'selected_recipes':len(selected),'first_contract_newly_passed':first_pass,
         'survivors':survivors,'counts':dict(counts),'stats':dict(STATS),'seconds':time.monotonic()-before,
         'split_budget_per_contract':64,'symbolic_fuel_per_branch':1000,'results':results,
         'scope':'Exhaustive interval branch coverage within finite symbolic budgets, composed box effects and existential spare suffix. No lower-bound or new machine claim.'}
    (ROOT/'root_experiments/split_guard_fold_results.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items()if k!='results'},indent=2))
