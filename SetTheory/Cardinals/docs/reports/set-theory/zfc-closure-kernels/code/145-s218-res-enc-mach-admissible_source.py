from pathlib import Path
from collections import deque,Counter
import json,sys
sys.path.insert(0,str(Path(__file__).resolve().parent/'support/k221/portable'));import source_language as s
rows=json.loads(Path(sys.argv[1]).read_text());G,_=s.graph_arithmetic(rows);assert G==s.graph_intervals(rows)
K=3;full=(1<<(K+1))-1
I=[None]*len(rows);I[0]=tuple(1<<min(v,K)for v in[3,0,0,0,3,0,0,0,0]);todo=deque([0])
def effect(mask,delta):
 out=0
 for v in range(K+1):
  if mask>>v&1:
   if delta==1:out|=1<<min(v+1,K)
   elif v==K:out|=(1<<(K-1))|(1<<K)
   else:out|=1<<max(v-1,0)
 return out

def successors(i,rs):
 (op,*args),tg=G[i]
 if op=='halt':return[]
 if op=='identity':return[(tg[0],rs)]
 a=args[0]
 if op=='increment':ss=list(rs);ss[a]=effect(ss[a],1);return[(tg[0],tuple(ss))]
 ans=[]
 if rs[a]&1:ss=list(rs);ss[a]=1;ans.append((tg[0],tuple(ss)))
 if rs[a]&~1:ss=list(rs);ss[a]=effect(rs[a]&~1,-1);ans.append((tg[1],tuple(ss)))
 return ans
while todo:
 i=todo.popleft()
 for j,r in successors(i,I[i]):
  old=I[j];v=r if old is None else tuple(a|b for a,b in zip(old,r))
  if v!=old:I[j]=v;todo.append(j)
# independently check seed inclusion and all abstract successors.
assert all(I[0][j]>>(min(v,K))&1 for j,v in enumerate([3,0,0,0,3,0,0,0,0]))
for i,r in enumerate(I):
 if r is None:continue
 for j,v in successors(i,r):assert all(a&b==a for a,b in zip(v,I[j]))
out=[];guards=Counter();text=[]
for i,(pc,op,a)in enumerate(rows):
 r=I[i]
 if r is None:continue
 mins=[next(v for v in range(K+1)if m>>v&1)for m in r]
 vals=[None]
 if op=='CD':
  vals=([0]if r[a]&1 else[])+([next(v for v in range(1,K+1)if r[a]>>v&1)]if r[a]&~1 else[])
  guards[('zero'if r[a]==1 else'positive'if not(r[a]&1)else'both')]+=1
 for v in vals:
  rr=list(mins)
  if v is not None:rr[a]=v
  text.append(f'{pc} {op} {a if a is not None else -1} '+ ' '.join(map(str,rr))+'\n')
 out.append({'index':i,'register_masks':r,'minimum_values':mins})
base=Path(sys.argv[2]);base.with_suffix('.json').write_text(json.dumps({'domain':'0,1,2,>=3 independently per register','seed':[3,0,0,0,3,0,0,0,0],'guard_counts':dict(guards),'reachable_sites':len(out),'cases':len(text),'facts':out},indent=2));base.with_suffix('.in').write_text(''.join(text));print('guards',guards,'reachable',len(out),'cases',len(text))
