from pathlib import Path
import sys,json,time,collections
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/'support/work/optimize196'))
import core
rows,labels=core.machine();cs=[c for c in core.contracts() if not(c[0]in(3774,3775)or(c[0]==3773 and c[1][1]==False))]
RAD=20;cx=collections.defaultdict(set);uses=collections.defaultdict(set);current=0
def take(segs,n):
 out=[]
 for x in segs:
  if x[0]=='b':out.append(x[1])
  elif x[0]=='r':
   out.extend([x[1]]*min(n-len(out),max(0,x[3])))
   if x[2] and len(out)<n:break
  else:out.append(0);break
  if len(out)>=n:break
 return tuple(out[:n])+(-1,)*max(0,n-len(out))
def obs(s):
 q,onl,l,r=s
 if(not onl and r and r[0][0]=='b'and(q not in core.BOXSTATES or q==113)):
  b=r[0][1];cx[q,b].add(tuple(reversed(take(l,RAD)))+take(r,RAD+1));uses[q,b].add(current)
start=time.time()
for i,c in enumerate(cs):
 current=i;assert core.run(rows,c,observe=obs)is not None
print('BASELINE',len(cs),'contexts',sum(map(len,cx.values())),'sec',time.time()-start,flush=True)
labels=sorted({q for q,b in rows});idx={q:i for i,q in enumerate(labels)}
with(ROOT/'reachable_fold_input.txt').open('w')as f:
 f.write(f'{len(labels)} {RAD} 100\n');f.write(' '.join(map(str,labels))+'\n')
 for q in labels:f.write(' '.join(str(v)for b in(0,1)for v in(rows[q,b][0],1 if rows[q,b][1]else-1,idx.get(rows[q,b][2],-1)))+'\n')
 for q in labels:
  for b in(0,1):
   vv=cx[q,b];f.write(str(len(vv))+'\n')
   for tp in sorted(vv,key=lambda v:v.count(-1),reverse=True):f.write(' '.join(map(str,tp))+'\n')
(ROOT/'reachable_fold_metadata.json').write_text(json.dumps({'contracts':len(cs),'omitted':[[3773,[2,False]],[3774,None],[3775,None]],'contexts':{f'{q}/{b}':len(v)for(q,b),v in cx.items()},'uses':{f'{q}/{b}':sorted(v)for(q,b),v in uses.items()}},indent=2))
