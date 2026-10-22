#!/usr/bin/env python3
"""Exhaust one-state, same-tape positive stuttering eliminations.

For q != p, remove q and redirect every target q to p. Check whether every
transition of q is simulated in the quotient by a nonempty block of at most
K transitions from p, with the same whole tape and head and mapped target.
Other states then simulate in one step. A success is an all-tape certificate;
failure only excludes this bounded, fixed-configuration-map proof template.
"""
import argparse, hashlib, json, time
from pathlib import Path

def parse(path):
    rows={}
    for line in Path(path).read_text().splitlines():
        if line.startswith('#') or not line.strip(): continue
        q,b,w,d,z=line.split(); rows[int(q),int(b)]=(int(w),1 if d=='R' else -1,int(z))
    return rows

def pattern(j,x):
    if j==0:return 0
    if j==1:return 1
    if j==2:return x&1
    if j==3:return (x//2)&1
    return ((x*x+7*x+11)*(j*3+1) >> ((x%5)+1))&1

def concrete(t,q,p,b,K,j):
    w,d,z=t[q,b]; z=p if z==q else z
    target={0:w}; a={0:b}; changes={}; state=p; head=0
    for step in range(1,K+1):
        sym=a.get(head,pattern(j,head))
        row=t.get((state,sym))
        if row is None:return False
        ww,dd,zz=row; a[head]=ww
        initial=b if head==0 else pattern(j,head)
        if ww==initial: changes.pop(head,None)
        else: changes[head]=ww
        head+=dd;state=p if zz==q else zz
        expected={} if b==w else target
        if state==z and head==d and changes==expected:return True
    return False

def symbolic(t,q,p,b,K):
    w,d,z=t[q,b];z=p if z==q else z
    todo=[(p,0,{0:b},{},0)]; count=0; maxsteps=0; terminals=[]
    expected={} if b==w else {0:w}
    while todo:
        state,head,env,changes,steps=todo.pop();count+=1
        if steps and state==z and head==d and changes==expected:
            terminals.append({'input':sorted(env.items()),'steps':steps});maxsteps=max(maxsteps,steps);continue
        if steps>=K:return False,{'reason':'step_bound','symbolic_nodes':count,'counterexample':sorted(env.items())}
        if head in changes: branches=[(changes[head],env)]
        elif head in env:branches=[(env[head],env)]
        else:branches=[(bb,dict(env,**{})) for bb in (0,1)]
        for sym,ee in branches:
            ee=ee.copy();ee.setdefault(head,sym)
            row=t.get((state,sym))
            if row is None:return False,{'reason':'premature_halt','symbolic_nodes':count,'counterexample':sorted(ee.items())}
            ww,dd,zz=row; cc=changes.copy()
            if ww==ee[head]:cc.pop(head,None)
            else:cc[head]=ww
            todo.append((p if zz==q else zz,head+dd,ee,cc,steps+1))
    return True,{'symbolic_nodes':count,'maximum_steps':maxsteps,'terminals':terminals}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('table');ap.add_argument('--steps',type=int,default=64);ap.add_argument('--out',default='elimination_results.json');a=ap.parse_args()
    raw=Path(a.table).read_bytes();t=parse(a.table);states=sorted({q for q,b in t});beg=time.time();tested=0;passing=[];symbolic_attempts=0;counts={};last=[]
    for q in states:
      for p in states:
        if q==p:continue
        tested+=1; fail=None
        for j in range(4):
          for b in (0,1):
            if not concrete(t,q,p,b,a.steps,j):fail=f'pattern{j}_read{b}';break
          if fail:break
        if fail:counts[fail]=counts.get(fail,0)+1;continue
        symbolic_attempts+=1;cert=[]
        for b in (0,1):
          ok,c=symbolic(t,q,p,b,a.steps);cert.append(c)
          if not ok:break
        if ok:passing.append({'removed':q,'representative':p,'branches':cert})
        else:last.append({'removed':q,'representative':p,'failure':c})
    result={'schema':'same-tape-state-elimination-v1','input':str(Path(a.table).resolve()),'sha256':hashlib.sha256(raw).hexdigest(),'states':len(states),'ordered_pairs':tested,'maximum_block_steps':a.steps,'concrete_prefilter_rejections':counts,'symbolic_attempts':symbolic_attempts,'symbolic_failures':last,'successes':passing,'seconds':time.time()-beg}
    Path(a.out).write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k not in ['symbolic_failures','successes']},indent=2));print('successes',len(passing))
if __name__=='__main__':main()
