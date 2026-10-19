"""Fresh interval induction over exact rotation240 register source, cap8."""
from pathlib import Path
from collections import deque,Counter
import json,hashlib,argparse
B=Path(__file__).resolve().parent
R=B.parent/'machines/sites_logical.json'
a=argparse.ArgumentParser();a.add_argument('--source',type=Path,default=R);a.add_argument('--cap',type=int,default=8);a.add_argument('--output',type=Path,default=B/'reachable_intervals8.json');args=a.parse_args();CAP=args.cap;INF=CAP+1;R=args.source
sites=json.loads(R.read_text());leaf={p:i for i,(p,k,a)in enumerate(sites)};prefix={p[:i]for p in leaf for i in range(len(p))};assert len(prefix)==len(leaf)-1 and not(prefix&leaf.keys())
assert all(p+b in prefix or p+b in leaf for p in prefix for b in'01')
def locate(p):
 while p not in leaf:
  assert p in prefix;p+='0'
 return leaf[p]
def inc(p):return p[:p.rindex('0')]+'1'if'0'in p else''
def strip(p,b,n):
 for j in range(len(p)-1,-1,-1):
  if p[j]==b:
   n-=1
   if n==0:return p[:j]
 return''
def succ(i):
 p,k,a=sites[i]
 if k=='CH':return{}
 if k=='CI':return {'inc':locate(inc(p))}
 if k=='CD':return {'positive':locate(inc(p)), 'zero':locate(inc(strip(p,'0',1)))}
 if k=='CB':return {'control':locate(inc(strip(p,'0',a)))}
 return {'control':locate(strip(p,'1',a))}
edges=[succ(i)for i in range(len(sites))]
def image(i,v,c):
 p,k,a=sites[i]
 if k in('CB','CC','CH'):return v
 lo,hi=v[a]
 if k=='CI':new=min(CAP,lo+1),min(INF,hi+1)
 elif c=='zero':
  if lo:return None
  new=0,0
 else:
  assert c=='positive'
  if hi==0:return None
  new=max(1,lo)-1,INF if hi==INF else hi-1
 return v[:a]+(new,)+v[a+1:]
def hull(a,b):
 if a is None:return b
 return tuple((min(x,z),max(y,w))for(x,y),(z,w)in zip(a,b))
def contains(a,b):return b is not None and all(x<=z and w<=y for(x,y),(z,w)in zip(a,b))
seed=(3,0,0,0,3,0,0,0,0);assert CAP>=3
initial=tuple((x,x)for x in seed);values=[None]*len(sites);root=locate('');values[root]=initial;queue=deque([root]);queued={root};updates=0
while queue:
 i=queue.popleft();queued.remove(i)
 for c,j in edges[i].items():
  im=image(i,values[i],c)
  if im is None:continue
  new=hull(values[j],im)
  if new!=values[j]:
   values[j]=new;updates+=1
   if j not in queued:queued.add(j);queue.append(j)
# Check every finite inductive obligation independently of worklist scheduling.
assert contains(values[root],initial)
checked=0;excluded=[];admitted=[];bounds=Counter()
for i,(p,k,a)in enumerate(sites):
 cs=['zero','positive']if k=='CD'else['halt']if k=='CH'else['inc']if k=='CI'else['control']
 for c in cs:
  im=None if values[i]is None else image(i,values[i],c)
  if im is None:excluded.append(dict(index=i,path=p,opcode=k,argument=a,guard=c));continue
  admitted.append(dict(index=i,path=p,opcode=k,argument=a,guard=c,intervals=values[i]))
  if c!='halt':assert contains(values[edges[i][c]],im),(i,c,edges[i][c]);checked+=1
 for r,v in enumerate(values[i]or[]):bounds[(r,*v)]+=1
report=dict(status='EXACT_SOURCE_INDUCTIVE_INTERVAL_PASS',source_sha256=hashlib.sha256(R.read_bytes()).hexdigest(),cap=CAP,infinity=INF,seed=seed,site_count=len(sites),updates=updates,checked_edges=checked,admitted_guarded_cases=len(admitted),excluded=excluded,unreachable_sites=[i for i,v in enumerate(values)if v is None],invariants=values,scope='Every finite prefix of the exact rotation240 register-source run from the displayed seed; successful finite interval closure is a mathematical induction certificate, not bounded testing. Does not by itself prove any modified binary table.')
args.output.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items()if k!='invariants'},indent=2))
