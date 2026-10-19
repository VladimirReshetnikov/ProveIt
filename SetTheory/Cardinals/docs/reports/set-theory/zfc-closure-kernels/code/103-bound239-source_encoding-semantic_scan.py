from pathlib import Path
from functools import cache
from collections import defaultdict
import json,itertools,random,time
H=Path(__file__).resolve().parent;D=json.loads((H/'mapping.json').read_text());S=D['structures'];N=len(S)
@cache
def size(n):return size(S[n][0])+size(S[n][1]) if isinstance(S[n][0],int) else 1

def increment(p):
 while p and p[-1]=='1':p=p[:-1]
 return p[:-1]+'1' if p else None

def execute(n,rs,limit=10000):
 r=list(rs);p=''
 for it in range(limit):
  k=n;i=0
  while isinstance(S[k][0],int):
   b=int(p[i]) if i<len(p) else 0;k=S[k][b];i+=1
  pp=p.ljust(i,'0')[:i];op,arg=S[k]
  if op=='CH':return ('halt',),tuple(r)
  if op=='CI':r[arg]+=1;p=increment(pp)
  elif op=='CD' and r[arg]>0:r[arg]-=1;p=increment(pp)
  elif op in ('CD','CB','CC'):
   count=1 if op=='CD' else arg;bit='1' if op=='CC' else '0'
   while count and pp:
    count-=pp[-1]==bit;pp=pp[:-1]
   if count:return (('continue' if op=='CC' else 'break'),count),tuple(r)
   p=pp if op=='CC' else increment(pp)
  if p is None:return ('normal',),tuple(r)
 return ('timeout',),tuple(r)

rnd=random.Random(16456);tests=[[0]*9]+[[int(j==i) for j in range(9)] for i in range(9)]+[[1]*9]+[[rnd.randrange(3) for _ in range(9)] for _ in range(20)]
groups=defaultdict(list);start=time.time();timeouts=[]
for n in range(N):
 if size(n)>80:continue
 sig=[]
 for rs in tests:
  e,r=execute(n,rs)
  if e==('timeout',):break
  sig.append((e,r))
 if len(sig)<len(tests):timeouts.append(n);continue
 groups[tuple(sig)].append(n)
results=[]
for ns in groups.values():
 if len(ns)>1:
  print(ns,[(n,size(n),[q for q,v in D['qnodes'].items()if v==[n]]) for n in ns])
  results.append(ns)
(H/'semantic_scan_results.json').write_text(json.dumps({'tests':tests,'groups':results,'timeouts':timeouts,'seconds':time.time()-start},indent=2)+'\n')
