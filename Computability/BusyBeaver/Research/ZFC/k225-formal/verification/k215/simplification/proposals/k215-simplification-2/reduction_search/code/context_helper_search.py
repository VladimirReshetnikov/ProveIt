#!/usr/bin/env python3
"""Bounded helper-reuse search under the eight exact K215 decoder prefixes.
No success implies neither semantic failure nor a state-count lower bound.
"""
from pathlib import Path
import argparse,collections,hashlib,json,time
p=argparse.ArgumentParser();p.add_argument('--inputs',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
root=a.inputs
def parse(path):
 t={}
 for line in path.read_text().splitlines():
  if not line or line.startswith('#'):continue
  q,b,w,d,z=line.split();t[int(q),int(b)]=(int(w),1 if d=='R' else -1,int(z))
 return t
old=parse(root/'primary.native.tm');T=parse(root/'cm215.native.tm')
source=json.loads((root/'sites215.json').read_text());prefixes=sorted({p[:i] for p,op,k in source for i in range(len(p))},key=lambda p:(len(p),p));cases=[]
for p in prefixes:
 tape={-1:1,**dict(enumerate(map(int,p)))};before=dict(tape);q=84;h=0
 for tick in range(1000):
  if h==len(p):break
  assert h in tape
  w,d,q=old[q,tape[h]];tape[h]=w;h+=d
 assert h==len(p) and tape==before
 if q in (52,176):cases.append((p,q))
assert len(cases)==8
states=sorted({q for q,b in T}-{176});nodes=0
bounds={'steps_after_first':500,'extra_cells':24,'nodes_per_case':16384}
def prove(action,case,allow176=False):
 global nodes
 p,oldq=case;goal=old[oldq,0][2];orig={-len(p)-1:1,**{i-len(p):int(v)for i,v in enumerate(p)},0:0};tape=dict(orig);w,d,q=action;tape[0]=w
 stack=[(q,d,tape,orig,0,frozenset())];count=0
 while stack:
  q,h,tape,orig,k,seen=stack.pop();count+=1;nodes+=1
  if count>bounds['nodes_per_case']:return 'branch_cap'
  if q==goal and h==1 and tape==orig:continue
  if k>=bounds['steps_after_first']:return 'step_cap'
  if q==176 and not allow176 or (q,0)not in T:return 'halt_or_missing'
  if h not in tape:
   if len(tape)>=len(p)+2+bounds['extra_cells']:return 'cell_cap'
   for bit in (0,1):
    nt=dict(tape);no=dict(orig);nt[h]=no[h]=bit;stack.append((q,h,nt,no,k,seen))
   continue
  state=(q,h,tuple(sorted(tape.items())))
  if state in seen:return 'repeat'
  seen=seen|{state};b=tape[h];w,d,z=action if q==52 and b==0 else T[q,b]
  nt=dict(tape);nt[h]=w;stack.append((z,h+d,nt,orig,k+1,seen))
 return 'PASS'
for case in cases:assert prove(T[52,0],case,True)=='PASS'
nodes=0;start=time.monotonic();stats=collections.Counter();hits=[];tried=0
for w in (0,1):
 for d in (-1,1):
  for q in states:
   tried+=1;act=(w,d,q);fail=None
   for i,case in enumerate(cases):
    outcome=prove(act,case)
    if outcome!='PASS':fail=(i,outcome);break
   if fail is None:hits.append(act);print('HIT',act,flush=True)
   else:stats[f'case{fail[0]}:{fail[1]}']+=1
result={'status':'COMPLETE_BOUNDED_SEARCH','tried':tried,'hits':hits,'bounds':bounds,'prefix_cases':[{'path':p,'old_state':q}for p,q in cases],'failure_counts':dict(stats),'symbolic_nodes':nodes,'seconds':time.monotonic()-start,'table_sha256':hashlib.sha256((root/'cm215.native.tm').read_bytes()).hexdigest(),'source_sha256':hashlib.sha256((root/'sites215.json').read_bytes()).hexdigest(),'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'scope':'Delete176, replace only52/0 by all856 actions; exact endpoint168 or154, head+1, all visited cells restored. Only known decoder prefixes assumed, arbitrary outside; bounded failures are inconclusive.'}
a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
