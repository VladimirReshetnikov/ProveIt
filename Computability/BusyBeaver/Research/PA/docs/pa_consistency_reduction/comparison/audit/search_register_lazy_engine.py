#!/usr/bin/env python3
"""Search register allocations lazily for direct folds into engine states.

Transported old observations are used as a heuristic filter. Any retained
candidate is verified again from every actual source frame and then must
have its literal startup checked; negatives are not claimed exhaustive.
"""
from pathlib import Path
import sys,time,json,collections
sys.path.insert(0,str(Path(__file__).resolve().parents[2]/'verification'));import symbolic as S
out=Path(__file__).parent;start=time.monotonic();base=S.load_machine();logical=list(S.PHYSICAL);entry={r:q for q,r in S.SKIPS.items()};states=sorted({q for q,b in base});protected={q for q,b in S.ENGINE_ROWS}|{base[k][2]for k in S.ENGINE_ROWS}|{0};keepers=sorted({q for q,b in S.ENGINE_ROWS});first=collections.defaultdict(list);cs=S.contracts();oldroot=S.ROOT
for i,branch,br,s,t in cs:
 trace=[]
 if S.execute(base,br,s,t,record=trace)is None:raise RuntimeError('baseline')
 seen=set()
 for tag,v,row in trace:
  q=v[0]
  if tag=='step'and q not in seen:first[q].append((br,v,t,i,branch));seen.add(q)
class Need(Exception):
 def __init__(self,r):self.r=r
class Machine:
 def __init__(self,q,r):self.drop,self.keep=q,r;self.perm=[-1]*9
 def reg(self,r):
  x=self.perm[r]
  if x<0:raise Need(r)
  return x
 def get(self,k,default=None):
  if k[0]==self.drop:return None
  v=base.get(k,default)
  if v is None:return None
  w,d,z=v
  if k not in S.ENGINE_ROWS and z in S.SKIPS:z=entry[self.reg(S.SKIPS[z])]
  return w,d,self.keep if z==self.drop else z
 def state(self,s,initial=False):
  if s is None:return None
  q,onl,left,right=s
  def seg(x):return('box',x[1],self.reg(x[2]))if x[0]=='box'and x[2]>=0 else x
  return(self.keep if initial or q==self.drop else q,onl,tuple(map(seg,left)),tuple(map(seg,right)))
 def branch(self,b):return None if b is None else(self.reg(b[0]),b[1])
hits=[];trials=0;executions=0;maxdepth=0
for drop in states:
 if drop in protected:continue
 for keep in keepers:
  if keep==drop:continue
  machine=Machine(drop,keep);examples=first[drop];solutions=[];visited=0
  def search(idx):
   global executions,maxdepth
   maxdepth=max(maxdepth,sum(x>=0 for x in machine.perm))
   while idx<len(examples):
    br,v,t,i,b=examples[idx]
    try:
     bv=machine.branch(br);sv=machine.state(v,True);tv=machine.state(t)
     executions+=1
     if S.execute(machine,bv,sv,tv)is None:return
    except Need as n:
     free=[r for r in range(9)if r not in machine.perm];free.sort(key=lambda r:r!=n.r)
     for r in free:
      machine.perm[n.r]=r;search(idx)
      if hits:return
     machine.perm[n.r]=-1;return
    idx+=1
   perm=list(machine.perm);free=[r for r in range(9)if r not in perm]
   for j in range(9):
    if perm[j]<0:
     r=j if j in free else free[0];free.remove(r);perm[j]=r
   nm={k:(w,d,entry[perm[S.SKIPS[z]]])if k not in S.ENGINE_ROWS and z in S.SKIPS else(w,d,z)for k,(w,d,z)in base.items()}
   nm={k:(w,d,keep if z==drop else z)for k,(w,d,z)in nm.items()if k[0]!=drop};S.PHYSICAL=[perm[r]for r in logical];S.ROOT=keep if drop==oldroot else oldroot
   try:summary,_=S.verify(nm)
   except AssertionError:return
   finally:S.PHYSICAL=list(logical);S.ROOT=oldroot
   hit={'drop':drop,'keep':keep,'permutation':perm,'summary':summary};hits.append(hit);stem=f'alloc_engine_{drop}_{keep}';hit['stem']=stem
   (out/(stem+'.tm')).write_text(''.join(f'{q} {b} {w} {"R"if d==1 else"L"} {z}\n'for(q,b),(w,d,z)in sorted(nm.items())))
   (out/(stem+'_sites.json')).write_text(json.dumps(S.all_sites())+'\n');print('HIT',hit,flush=True)
  search(0);trials+=1
  if hits:break
 print('drop',drop,'trials',trials,'executions',executions,'seconds',round(time.monotonic()-start,1),flush=True)
 if hits:break
(out/'register_lazy_engine_results.json').write_text(json.dumps({'trials':trials,'symbolic_executions':executions,'max_assigned_registers':maxdepth,'hits':hits,'seconds':time.monotonic()-start},indent=2)+'\n');print('DONE',hits,flush=True)
