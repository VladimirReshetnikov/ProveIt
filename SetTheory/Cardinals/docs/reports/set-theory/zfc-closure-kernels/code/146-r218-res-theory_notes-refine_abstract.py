#!/usr/bin/env python3
from pathlib import Path
from collections import deque
import argparse,json,hashlib,time
from audit_abstract_certificate import compile_cfg,need

def infer(rows,cutoff):
 cfg=compile_cfg(rows);domains=[None]*len(rows)
 domains[0]=[1<<min(v,cutoff)for v in [3,0,0,0,3,0,0,0,0]]
 todo=deque([0]);queued={0};processed=0;point=(1<<cutoff)-1;tail=1<<cutoff
 def inc(m):return((m&point)<<1)|(tail if m&tail else 0)
 def dec(m):return((m&point)>>1)|((tail|(tail>>1))if m&tail else 0)
 def propagate(j,dd):
  old=domains[j];new=dd if old is None else[a|b for a,b in zip(old,dd)]
  if old!=new:
   domains[j]=new
   if j not in queued:todo.append(j);queued.add(j)
 while todo:
  i=todo.popleft();queued.remove(i);processed+=1
  d=domains[i];p,op,r=rows[i];targets=cfg[i]
  if op=='CI':
   dd=list(d);dd[r]=inc(dd[r]);propagate(targets[0],dd)
  elif op=='CD':
   if d[r]&1:
    dd=list(d);dd[r]=1;propagate(targets[0],dd)
   if d[r]&~1:
    dd=list(d);dd[r]=dec(dd[r]);propagate(targets[1],dd)
  else:
   for j in targets:propagate(j,d)
 dead=[i for i,d in enumerate(domains)if d is None]
 zero=[i for i,((_,op,r),d)in enumerate(zip(rows,domains))if op=='CD'and d is not None and d[r]==1]
 pos=[i for i,((_,op,r),d)in enumerate(zip(rows,domains))if op=='CD'and d is not None and d[r]&1==0]
 return dict(summary=dict(cutoff=cutoff,processed=processed,unreachable=dead,zero_cd=zero,positive_cd=pos),domains=domains)

if __name__=='__main__':
 p=Path(__file__).resolve().parents[1];rows=json.loads((p/'baseline220/K220_Construction_2026-10-20/machine/sites220.json').read_text())
 for k in (8,16,32,64):
  t=time.time();r=infer(rows,k);r['summary']['seconds']=time.time()-t
  (p/f'theory_notes/abstract_cutoff{k}.json').write_text(json.dumps(r)+'\n');print(r['summary'],flush=True)
