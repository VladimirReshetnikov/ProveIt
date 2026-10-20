import json,collections
from pathlib import Path
rows=json.loads(Path('Computability/BusyBeaver/Research/ZFC/candidate-k219/sites219.json').read_text());d={p:(op,arg) for p,op,arg in rows}
def parse(p=''):return d[p] if p in d else (parse(p+'0'),parse(p+'1'))
tree=parse()
def leaf(t):return isinstance(t[0],str)
def leaves(t,p=''):
 if leaf(t):return [(p,*t)]
 return leaves(t[0],p+'0')+leaves(t[1],p+'1')
def graph(rows):
 ranges={}
 for i,(p,*_) in enumerate(rows):
  for k in range(len(p)+1):
   q=p[:k]
   if q not in ranges:ranges[q]=[i,i+1]
   else:ranges[q][1]=i+1
 def target(p,b,k):
  for j in range(len(p)-1,-1,-1):
   if p[j]==b:
    k-=1
    if k==0:return ranges[p[:j]][int(b=='0')]
  return ('B' if b=='0' else 'C',k)
 g=[]
 for i,(p,op,arg) in enumerate(rows):
  g.append((op,arg,(i+1,) if op=='CI' else (target(p,'0',1),i+1) if op=='CD' else (target(p,'0',arg),) if op=='CB' else (target(p,'1',arg),) if op=='CC' else ()))
 return g
G=graph(rows);assert all(isinstance(t,int) and t<len(G) for _,_,ts in G for t in ts)
# finite Cartesian abstraction; bucket8 denotes all naturals>=8.
K=8;full=(1<<(K+1))-1
states=[None]*len(rows);states[0]=tuple(1<<x for x in [3,0,0,0,3,0,0,0,0]);todo=collections.deque([0]);updates=0
def transfer(pc,s):
 op,r,ts=G[pc]
 if op=='CH':return []
 if op in ('CB','CC'):return [(ts[0],s)]
 if op=='CI':
  v=list(s);v[r]=((s[r]<<1)&full)|(s[r]&(1<<K));return [(ts[0],tuple(v))]
 out=[]
 if s[r]&1:
  v=list(s);v[r]=1;out.append((ts[0],tuple(v)))
 if s[r]&~1:
  v=list(s);v[r]=(s[r]>>1)|(s[r]&(1<<K));out.append((ts[1],tuple(v)))
 return out
while todo:
 i=todo.popleft()
 for j,v in transfer(i,states[i]):
  new=v if states[j] is None else tuple(a|b for a,b in zip(states[j],v))
  if states[j]!=new:states[j]=new;todo.append(j);updates+=1
assert all(states[j] is not None and all(x&~y==0 for x,y in zip(v,states[j])) for i,s in enumerate(states) if s is not None for j,v in transfer(i,s))
print('dead', [i for i,s in enumerate(states) if s is None], 'updates',updates)
# local/global single rotations and control match under invariant
nodes=[];seen=set()
def visit(t):
 if t in seen:return
 seen.add(t)
 if not leaf(t):visit(t[0]);visit(t[1])
 nodes.append(t)
visit(tree)
def replace(t,a,b):
 if t==a:return b
 return t if leaf(t) else (replace(t[0],a,b),replace(t[1],a,b))
def nset(t):
 s=set()
 def go(t):
  if t in s:return
  s.add(t)
  if not leaf(t):go(t[0]);go(t[1])
 go(t);return s
hits=[];scores=collections.Counter();tries=0
for ni,n in enumerate(nodes):
 if leaf(n):continue
 a,b=n
 cand=[]
 if not leaf(a):cand.append(('R',(a[0],(a[1],b))))
 if not leaf(b):cand.append(('L',((a,b[0]),b[1])))
 for kind,m in cand:
  z=replace(tree,n,m);rr=leaves(z);gg=graph(rr);tries+=1
  delta=[];reachdelta=[]
  for i,(g,h) in enumerate(zip(G,gg)):
   if g!=h:
    delta.append(i)
    if states[i] is not None:
     enabled=range(len(g[2])) if g[0]!='CD' else [b for b in (0,1) if states[i][g[1]] & (1 if b==0 else ~1)]
     if any(g[2][k]!=h[2][k] for k in enabled):reachdelta.append(i)
  if not reachdelta:
   score=len(nset(z));scores[score]+=1
   hits.append({'node':ni,'direction':kind,'score':score,'changed':delta,'syntactic':not delta,'tree':z})
print('global',tries,dict(scores),'hits',len(hits))
for h in hits:
 if h['score']<=206:print({k:v for k,v in h.items() if k!='tree'})
json.dump({'rows':rows,'states':states,'nodes':nodes,'hits':[{k:v for k,v in h.items() if k!='tree'} for h in hits]},open('/tmp/k219-probe.json','w'))
