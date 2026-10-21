"""Independent small K219 source model; no compiler or delivered modules imported.

Nonnegative control targets are leaf ordinals. Negative local exits are
-1=Normal, -2k=Break(k), and -(2k+1)=Continue(k). Full-program exits restart0.
"""
from pathlib import Path
from functools import lru_cache
import functools,json,collections,hashlib
HERE=Path(__file__).resolve().parent
BASE=HERE.parent/'inputs'
def leaf(t):return isinstance(t[0],str)
def freeze(t):return tuple(map(freeze,t)) if isinstance(t,list) else t
def leaves(t,p=''):
 return [(p,*t)] if leaf(t) else leaves(t[0],p+'0')+leaves(t[1],p+'1')
def parse(rows):
 dd={p:(o,a) for p,o,a in rows};assert len(dd)==len(rows)
 def go(p=''):
  if p in dd:return dd[p]
  assert any(q.startswith(p+'0') for q in dd) and any(q.startswith(p+'1') for q in dd)
  return go(p+'0'),go(p+'1')
 t=go();assert [list(r) for r in leaves(t)]==[list(r) for r in rows];return t
def nodes(t):
 seen=set();order=[]
 def go(t):
  if t in seen:return
  seen.add(t)
  if not leaf(t):go(t[0]);go(t[1])
  order.append(t)
 go(t);return order
def replace(t,old,new):
 return new if t==old else t if leaf(t) else (replace(t[0],old,new),replace(t[1],old,new))
def metrics(t):
 rr=leaves(t)
 return dict(dag_nodes=len(nodes(t)),leaf_occurrences=len(rr),maximum_depth=max(len(p) for p,_,_ in rr),maximum_zero_run=max(len(z) for p,_,_ in rr for z in p.split('1')))
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
    if k==0:return ranges[p[:j]][int(b=='0')]%len(rows)
  return 0
 g=[]
 for i,(p,o,r) in enumerate(rows):
  ts=((i+1)%len(rows),) if o=='CI' else (target(p,'0',1),(i+1)%len(rows)) if o=='CD' else (target(p,'0',r),) if o=='CB' else (target(p,'1',r),) if o=='CC' else ()
  assert o in ('CI','CD','CB','CC','CH');g.append((o,r,ts))
 return g
def arithmetic_graph(rows):
 lookup={p:i for i,(p,_,_) in enumerate(rows)};depth=max(map(len,lookup))
 def direct(p):
  q=p+'0'*(depth+1)
  for k in range(1,len(q)+1):
   if q[:k] in lookup:
    assert '1' not in p[k:];return lookup[q[:k]]
  raise AssertionError(p)
 def inc(p):return format((int(p,2)+1)%2**len(p),f'0{len(p)}b') if p else ''
 def cut(p,b,k):
  js=[j for j,x in enumerate(p) if x==b];return p[:js[-k]] if len(js)>=k else ''
 g=[]
 for p,o,r in rows:
  ts=(direct(inc(p)),) if o=='CI' else (direct(inc(cut(p,'0',1))),direct(inc(p))) if o=='CD' else (direct(inc(cut(p,'0',r))),) if o=='CB' else (direct(cut(p,'1',r)),) if o=='CC' else ()
  g.append((o,r,ts))
 return g
@lru_cache(None)
def boundary(t):
 if leaf(t):return (1,0) if t[0]=='CD' else (t[1],0) if t[0]=='CB' else (0,t[1]) if t[0]=='CC' else (0,0)
 a,b=boundary(t[0]),boundary(t[1]);return max(a[0]-1,b[0],0),max(a[1],b[1]-1,0)
def load():
 raw=(BASE/'sites218.json').read_bytes();rr=json.loads(raw);t=parse(rr)
 assert metrics(t)==dict(dag_nodes=205,leaf_occurrences=4744,maximum_depth=38,maximum_zero_run=6)
 assert graph(rr)==arithmetic_graph(rr)
 return t,rr
N=9
ID=tuple(tuple(int(i==j) for j in range(N))+ (0,) for i in range(N))
def compose(a,b): # execute a then b
 return tuple(tuple(sum(b[i][k]*a[k][j] for k in range(N))+(b[i][N] if j==N else 0) for j in range(N+1)) for i in range(N))
@functools.lru_cache(None)
def localg(t):
 if leaf(t):
  op,r=t;return ((op,r,(-1,) if op=='CI' else (-2,-1) if op=='CD' else (-2*r,) if op=='CB' else (-2*r-1,) if op=='CC' else ()),)
 aa,bb=localg(t[0]),localg(t[1]);la=len(aa)
 def tr(q,side):
  if q>=0:return q+(la if side else 0)
  if side==0:
   if q==-1:return la
   if q%2==0:return -1 if q==-2 else q+2
   return q
  if q < -1 and q%2:return 0 if q==-3 else q+2
  return q
 return tuple((o,r,tuple(tr(q,0) for q in ts)) for o,r,ts in aa)+tuple((o,r,tuple(tr(q,1) for q in ts)) for o,r,ts in bb)
@functools.lru_cache(None)
def affine(t):
 if leaf(t):
  if t[0]!='CI':return None
  a=[list(r) for r in ID];a[t[1]][N]+=1;return tuple(map(tuple,a))
 a,b=affine(t[0]),affine(t[1])
 if a is not None and b is not None:return compose(a,b)
 gg=localg(t)
 op,r,ts=gg[0]
 if op!='CD' or ts[0]!=-1:return None
 pc=ts[1];seen=set();incs=[0]*N
 while pc!=0:
  if pc<0 or pc in seen:return None
  seen.add(pc);op,q,ts=gg[pc]
  if op=='CI':incs[q]+=1
  elif op not in ('CB','CC'):return None
  pc=ts[0]
 if incs[r]:return None
 a=[list(row) for row in ID];a[r]=[0]*(N+1)
 for s in range(N):a[s][r]+=incs[s]
 return tuple(map(tuple,a))
