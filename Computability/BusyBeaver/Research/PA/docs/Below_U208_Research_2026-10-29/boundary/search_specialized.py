from pathlib import Path
import json,itertools,time,sys
ROOT=Path(__file__).resolve().parent
BASE=ROOT/'baseline'
sys.path.insert(0,str(BASE/'code'));from build import read
T=read(BASE/'machine/u208.native.tm');data=json.loads((ROOT/'specialized_windows.json').read_text());R=data['radius'];W={int(q):v for q,v in data['contexts'].items()};states=sorted(W)
def exact(old,new,q,keep,remove,word,limit=30):
 vals={i-R:(word>>i)&1 for i in range(2*R+1)}; b=vals[0];w,d,z=old[q,b];z=keep if z==remove else z
 stack=[(keep,0,{},vals,0)]
 while stack:
  s,h,writes,vals,k=stack.pop()
  if k and (s,h)==(z,d):
   if all(writes.get(x,vals.get(x,('v',x)))==(w if x==0 else vals.get(x,('v',x))) for x in set(writes)|{0}):continue
  if s==254 or k>=limit:return False
  b=writes.get(h,vals.get(h))
  if b is None:
   for bit in (0,1):nv=dict(vals);nv[h]=bit;stack.append((s,h,writes.copy(),nv,k))
   continue
  a,e,j=new[s,b];nw=writes.copy();nw[h]=a;stack.append((j,h+e,nw,vals,k+1))
  if len(stack)>1024:return False
 return True
results=[];trials=0;pairs=0;start=time.time()
for remove in states:
 if remove==0:continue
 for keep in states:
  if keep>=remove or keep==0:continue
  nt={(q,b):(w,d,keep if z==remove else z) for (q,b),(w,d,z) in T.items() if q!=remove}
  eq=[b for b in (0,1) if (T[remove,b][0],T[remove,b][1],keep if T[remove,b][2]==remove else T[remove,b][2])==nt[keep,b]]
  if not eq:continue
  pairs+=1
  branches=[1-eq[0]] if len(eq)==1 else [0,1]
  cases=[(q,v) for q in (remove,keep) for v in W[q]]
  # Alternating extreme windows from each read/state accelerates rejection only.
  fast=[]
  for q in (remove,keep):
   for b in (0,1):
    vs=[v for v in W[q] if (v>>R)&1==b]
    for v in (vs[:1]+vs[-1:]):
     if(q,v)not in fast:fast.append((q,v))
  for branch in branches:
   oldrow=nt[keep,branch]
   for z in states+[254]:
    if z==remove:continue
    for w,d in itertools.product((0,1),(-1,1)):
     nt[keep,branch]=(w,d,z);trials+=1
     if not all(exact(T,nt,q,keep,remove,v) for q,v in fast):continue
     if not all(exact(T,nt,q,keep,remove,v) for q,v in cases):continue
     result={'remove':remove,'keep':keep,'branch':branch,'row':[w,d,z]};results.append(result);print('FOUND',result,flush=True)
     (ROOT/f'candidate_{remove}_{keep}_{branch}_{w}_{d}_{z}.tm').write_text(''.join(f'{q} {b} {a} {"R" if e==1 else "L"} {j}\n' for (q,b),(a,e,j) in sorted(nt.items())))
   nt[keep,branch]=oldrow
 print('STATE',remove,pairs,trials,time.time()-start,flush=True)
(ROOT/'specialized_search.json').write_text(json.dumps({'pairs':pairs,'action_trials':trials,'results':results,'seconds':time.time()-start,'limit':30},indent=2)+'\n')
