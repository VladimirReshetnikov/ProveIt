import json,time
from collections import Counter
import price_sources as P
D=P.D;T={}
p=D.D/'shared_cancellation/candidate.native.tm'
for line in p.read_text().splitlines():
 if line and not line.startswith('#'):
  q,b,w,m,z=line.split();T[int(q),int(b)]=(int(w),1 if m=='R'else-1,int(z))
t=P.tree(json.load(open(D.D.parent/'research218_source/shared_cancellation_sites.json')));groups,paths,gates=P.allocation(T,t);counts=Counter();results=[];near=[];began=time.monotonic()
for role in(303,304):
 occ=[p for p,q in paths.items()if q==role];options=[]
 for entry in sorted({q for q,b in T}-{303,304}):
  proofs=[];ok=True;branch_counts=Counter()
  for path in occ:
   for b in(0,1):
    cells={-1:1,**{i:int(c)for i,c in enumerate(path+str(b))}};initial=cells.copy();q=entry;h=len(path);trace=[];seen=set();goal=T[role,b][2]
    for k in range(32):
     if q in(254,303,304)or h not in cells:break
     key=q,h,tuple(cells.items())
     if key in seen:break
     seen.add(key);read=cells[h];w,m,z=T[q,read];trace.append([q,h,read,w,m,z]);cells[h]=w;h+=m;q=z;counts['transitions']+=1
     if h==len(path)+1 and q==goal and cells==initial:proofs.append(dict(path=path,read=b,trace=trace));branch_counts[b]+=1;break
    else:counts['step_cap']+=1
    if not trace or not(h==len(path)+1 and q==goal and cells==initial):ok=False
   pass
  counts['entries']+=1
  if any(branch_counts[b]==len(occ)for b in(0,1)):near.append(dict(role=role,entry=entry,branch_counts=dict(branch_counts),occurrences=len(occ)))
  if ok:options.append(dict(entry=entry,proofs=proofs,max_steps=max(len(x['trace'])for x in proofs)))
 results.append(dict(role=role,occurrences=len(occ),options=options));print('ROLE',role,'options',[x['entry']for x in options],flush=True)
D.dump('ROLE_ENTRY_HALF_RESULT.json',dict(results=results,near=near,counts=dict(counts),seconds=time.monotonic()-began,table_sha256=D.H(p.read_bytes()),scope='Exact-prefix alias proof only; proposed right CI6 engine82 is not semantically verified'))
