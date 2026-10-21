#!/usr/bin/env python3
"""Search head-offset quotients q@(x) -> p@(x+h), h = -2 or +2.

Only edges into the removed q change: their target becomes p and their move
becomes move+h. All such retained edges must still have move +/-1. A removed
q-step is matched by a nonempty bounded block with the identical whole tape
and mapped final head/control. The initial control is not removed.
"""
from search_elimination import parse,pattern
from pathlib import Path
import argparse,json,time,hashlib

def concrete(t,q,p,h,b,K,j):
    w,d,z=t[q,b]; targethead=d+(h if z==q else 0);z=p if z==q else z
    expected={} if b==w else {0:w};a={0:b}; changes={};state=p;head=h
    for steps in range(1,K+1):
        sym=a.get(head,pattern(j,head));row=t.get((state,sym))
        if row is None:return False
        ww,dd,zz=row
        if zz==q:dd+=h;zz=p
        assert dd in (-1,1)
        a[head]=ww;init=b if head==0 else pattern(j,head)
        if ww==init:changes.pop(head,None)
        else:changes[head]=ww
        head+=dd;state=zz
        if state==z and head==targethead and changes==expected:return True
    return False

def symbolic(t,q,p,h,b,K):
    w,d,z=t[q,b];targethead=d+(h if z==q else 0);z=p if z==q else z
    expected={} if b==w else {0:w};todo=[(p,h,{0:b},{},0)];count=0;terminals=[]
    while todo:
        state,head,env,changes,steps=todo.pop();count+=1
        if steps and state==z and head==targethead and changes==expected:
            terminals.append({'input':sorted(env.items()),'steps':steps});continue
        if steps>=K:return False,{'reason':'step_bound','symbolic_nodes':count,'counterexample':sorted(env.items())}
        if head in changes:branches=[(changes[head],env)]
        elif head in env:branches=[(env[head],env)]
        else:branches=[(0,env),(1,env)]
        for sym,ee in branches:
            ee=ee.copy();ee.setdefault(head,sym);row=t.get((state,sym))
            if row is None:return False,{'reason':'premature_halt','symbolic_nodes':count,'counterexample':sorted(ee.items())}
            ww,dd,zz=row
            if zz==q:dd+=h;zz=p
            assert dd in (-1,1)
            cc=changes.copy()
            if ww==ee[head]:cc.pop(head,None)
            else:cc[head]=ww
            todo.append((zz,head+dd,ee,cc,steps+1))
    return True,{'symbolic_nodes':count,'maximum_steps':max(x['steps'] for x in terminals),'terminals':terminals}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('table');ap.add_argument('--steps',type=int,default=128);ap.add_argument('--out',default='offset_results.json');a=ap.parse_args()
    raw=Path(a.table).read_bytes();t=parse(a.table);states=sorted({q for q,b in t});beg=time.time();elig=[];tested=0;attempts=0;counts={};passing=[];failures=[]
    for q in states:
        if q==0:continue
        dirs={d for (qq,b),(w,d,z) in t.items() if z==q and qq!=q}
        if len(dirs)!=1:continue
        h=-2*next(iter(dirs));elig.append([q,h])
        for p in states:
            if q==p:continue
            tested+=1;fail=None
            for j in range(4):
                for b in (0,1):
                    if not concrete(t,q,p,h,b,a.steps,j):fail=f'pattern{j}_read{b}';break
                if fail:break
            if fail:counts[fail]=counts.get(fail,0)+1;continue
            attempts+=1;cert=[]
            for b in (0,1):
                ok,c=symbolic(t,q,p,h,b,a.steps);cert.append(c)
                if not ok:break
            if ok:passing.append({'removed':q,'representative':p,'head_offset':h,'branches':cert})
            else:failures.append({'removed':q,'representative':p,'head_offset':h,'failure':c})
    result={'schema':'head-offset-state-elimination-v1','input':str(Path(a.table).resolve()),'sha256':hashlib.sha256(raw).hexdigest(),'states':len(states),'eligible_removed_states':elig,'ordered_pairs':tested,'maximum_block_steps':a.steps,'concrete_prefilter_rejections':counts,'symbolic_attempts':attempts,'symbolic_failures':failures,'successes':passing,'seconds':time.time()-beg}
    Path(a.out).write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k not in ['eligible_removed_states','symbolic_failures','successes']},indent=2));print('eligible',len(elig),'successes',len(passing))
if __name__=='__main__':main()
