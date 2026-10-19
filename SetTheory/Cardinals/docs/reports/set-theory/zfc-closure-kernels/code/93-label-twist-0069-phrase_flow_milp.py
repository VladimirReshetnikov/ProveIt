#!/usr/bin/env python3
"""Finite-candidate exact shared-grammar optimization; discovery only."""
from pathlib import Path
from collections import Counter,defaultdict
import argparse,json,time
import numpy as np
from scipy.optimize import milp,Bounds,LinearConstraint
from scipy.sparse import coo_matrix

p=argparse.ArgumentParser();p.add_argument('--maxlen',type=int,default=20);p.add_argument('--seconds',type=int,default=120);p.add_argument('--output',default='fine-milp.json');p.add_argument('--bound',type=int,default=127);p.add_argument('--new-ax',default=None);args=p.parse_args()
base=Path(__file__).resolve().parent
g=json.loads((base/'grammar245.json').read_text());enc=json.loads((base/'fine_encoding.json').read_text())
fm=enc['atom_expansions'];ex=lambda w:''.join(fm[c]for c in w)
rules={ex(w):(ex(a),ex(b))for w,a,b in g['rules']}
allowed={}
lines=(base/'fine-route-grammar.txt').read_text().splitlines();n,nr,na=map(int,lines[0].split())
for row in lines[n+nr+1:]:
 if row.strip():
  w,b=row.split();allowed[w]=int(b)
roots={ex(w)for w in g['roots']}|{ex(r['word'])for r in g['routes']}
if args.new_ax:
 oldax=max(roots,key=len);newax=Path(args.new_ax).read_text().strip();assert len(newax)==len(oldax);roots.remove(oldax);roots.add(newax);rules[newax]=rules.pop(oldax)
frozen={}
for row in (base/'fine-bootstrap-lock54.txt').read_text().splitlines()[1:]:
 if row.strip():
  w,b,t=row.split();frozen[w]=rules[w]
lines=(base/'fine-route-constraints.txt').read_text().splitlines();ng=int(lines[0]);i=1
for j in range(ng):
 src,b,oldroot,nc=lines[i].split();i+=1
 root=next(ex(r['word'])for r in g['routes']if r['source']==int(src)and r['read']==int(b))
 for c in range(int(nc)):
  bits,target=lines[i].split();i+=1;w=root
  for bit in bits:
   frozen[w]=rules[w];w=rules[w][int(bit)]
  assert w==target
freq=Counter()
for w in roots:
 for length in range(2,min(len(w),args.maxlen)+1):
  freq.update(w[k:k+length]for k in range(len(w)-length+1))
pool=set(rules)|set(allowed)|roots|{w for w,c in freq.items()if c>=2}
pool={w for w in pool if w not in allowed}
active=set(pool)|set(allowed)
words=sorted(pool,key=lambda w:(len(w),w));wi={w:i for i,w in enumerate(words)};nwords=len(words)
trie={}
for v in active:
 d=trie
 for t in v:d=d.setdefault(t,{})
 d[None]=v
edges=[];groups=[]
for w in words:
 group=[]
 if w in frozen:
  a,b=frozen[w]
  assert w==a+b
  for start,end,child in [(0,len(a),a),(len(a),len(w),b)]:
   group.append(len(edges));edges.append((w,start,end,child))
 else:
  for i in range(len(w)):
   d=trie
   for j in range(i,len(w)):
    if w[j]not in d:break
    d=d[w[j]]
    if None not in d:continue
    child=d[None]
    if child==w:continue
    if child in allowed and ((i==0 and not allowed[child]&1)or(j==len(w)-1 and not allowed[child]&2)):continue
    group.append(len(edges));edges.append((w,i,j+1,child))
 groups.append(group)
ne=len(edges);nv=nwords+ne;c=np.ones(nv);c[:nwords]=-1
rows=[];cols=[];values=[];lo=[];hi=[]
def constraint(items,l,h):
 r=len(lo);lo.append(l);hi.append(h)
 for col,v in items:rows.append(r);cols.append(col);values.append(v)
for w,group in zip(words,groups):
 inflow=defaultdict(list);outflow=defaultdict(list)
 for j in group:
  _,start,end,child=edges[j];x=nwords+j
  inflow[end].append(x);outflow[start].append(x)
  if child not in allowed:constraint([(x,1),(wi[child],-1)],-np.inf,0)
 for pos in sorted(set(inflow)|set(outflow)|{0,len(w)}):
  items=[(x,1)for x in outflow[pos]]+[(x,-1)for x in inflow[pos]]
  if pos==0:items.append((wi[w],-1))
  elif pos==len(w):items.append((wi[w],1))
  constraint(items,0,0)
for w in roots:constraint([(wi[w],1)],1,1)
constraint([(i,c[i])for i in range(nv)],-np.inf,args.bound)
mat=coo_matrix((values,(rows,cols)),shape=(len(lo),nv)).tocsc()
print(json.dumps(dict(words=nwords,flow_edges=ne,constraints=len(lo),roots=len(roots),frozen=len(frozen),bound=args.bound)),flush=True)
t=time.monotonic();res=milp(c,integrality=np.ones(nv),bounds=Bounds(0,1),constraints=LinearConstraint(mat,np.array(lo),np.array(hi)),options=dict(time_limit=args.seconds,mip_rel_gap=0))
report=dict(status=int(res.status),message=res.message,seconds=time.monotonic()-t,fun=res.fun,mip_gap=getattr(res,'mip_gap',None),lower_bound=getattr(res,'mip_dual_bound',None),pool_size=nwords,flow_edge_count=ne,scope='Finite phrase-flow model with fixed routes/bootstrap; discovery result, no runtime claim.')
if res.x is not None:
 phrases={}
 for w,group in zip(words,groups):
  if res.x[wi[w]]<.5:continue
  chosen=sorted([edges[j][1:]for j in group if res.x[nwords+j]>.5]);pos=0;children=[]
  for start,end,child in chosen:assert start==pos;pos=end;children.append(child)
  assert pos==len(w)and len(children)>=2 and ''.join(children)==w
  phrases[w]=children
 assert sum(len(v)-1 for v in phrases.values())==round(res.fun)
 report.update(phrase_cost=sum(len(v)-1 for v in phrases.values()),phrases=phrases,roots=sorted(roots),routes=[dict(r,word=ex(r['word']))for r in g['routes']],properties=[],erase177=True,retarget=-2,framework_states=118)
(base/args.output).write_text(json.dumps(report,indent=2)+'\n')
print({k:v for k,v in report.items()if k not in['phrases','roots','routes']},flush=True)
