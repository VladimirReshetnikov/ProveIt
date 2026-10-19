#!/usr/bin/env python3
"""Finite-candidate exact shared-grammar optimization; discovery only."""
from pathlib import Path
from collections import Counter,defaultdict
import argparse,json,time
import numpy as np
from scipy.optimize import milp,Bounds,LinearConstraint
from scipy.sparse import coo_matrix

p=argparse.ArgumentParser();p.add_argument('--maxlen',type=int,default=20);p.add_argument('--seconds',type=int,default=120);p.add_argument('--output',default='fine-milp.json');p.add_argument('--bound',type=int,default=127);args=p.parse_args()
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
pool=set(rules)|set(allowed)|{w for w,c in freq.items()if c>=2}
pool={w for w in pool if w not in allowed}
active=set(pool)|set(allowed)
opts={}
for w in pool:
 options=[]
 for k in range(1,len(w)):
  a,b=w[:k],w[k:]
  if a not in active or b not in active:continue
  if a in allowed and not allowed[a]&1:continue
  if b in allowed and not allowed[b]&2:continue
  if w in frozen and(a,b)!=frozen[w]:continue
  options.append((a,b))
 opts[w]=options
# Repeatedly remove words with no supported derivation.
while True:
 bad={w for w,o in opts.items()if not o}
 if not bad:break
 for w in bad:del opts[w]
 for w in opts:opts[w]=[(a,b)for a,b in opts[w]if a not in bad and b not in bad]
 assert not bad&roots
words=sorted(opts,key=lambda w:(len(w),w));wi={w:i for i,w in enumerate(words)}
productions=[(w,a,b)for w in words for a,b in opts[w]]
nwords=len(words);nv=nwords+len(productions);c=np.zeros(nv);c[:nwords]=1
rows=[];cols=[];values=[];lo=[];hi=[]
def constraint(items,l,h):
 r=len(lo);lo.append(l);hi.append(h)
 for col,v in items:rows.append(r);cols.append(col);values.append(v)
byp=defaultdict(list)
for j,(w,a,b)in enumerate(productions):
 x=nwords+j;byp[w].append(x)
 for child in (a,b):
  if child not in allowed:constraint([(x,1),(wi[child],-1)],-np.inf,0)
for w in words:constraint([(wi[w],-1)]+[(j,1)for j in byp[w]],0,0)
for w in roots:constraint([(wi[w],1)],1,1)
constraint([(i,1)for i in range(nwords)],-np.inf,args.bound)
mat=coo_matrix((values,(rows,cols)),shape=(len(lo),nv)).tocsc()
print(json.dumps(dict(words=nwords,productions=len(productions),constraints=len(lo),roots=len(roots),frozen=len(frozen),bound=args.bound)),flush=True)
t=time.monotonic();res=milp(c,integrality=np.ones(nv),bounds=Bounds(0,1),constraints=LinearConstraint(mat,np.array(lo),np.array(hi)),options=dict(time_limit=args.seconds,mip_rel_gap=0))
report=dict(status=int(res.status),message=res.message,seconds=time.monotonic()-t,fun=res.fun,mip_gap=getattr(res,'mip_gap',None),lower_bound=getattr(res,'mip_dual_bound',None),pool_size=nwords,production_count=len(productions),scope='Finite candidate model with fixed routes/bootstrap; discovery result, no runtime claim.')
if res.x is not None:
 newrules=[(w,a,b)for j,(w,a,b)in enumerate(productions)if res.x[nwords+j]>.5]
 report.update(rules_count=len(newrules),rules=newrules,roots=sorted(roots),routes=[dict(r,word=ex(r['word']))for r in g['routes']],properties=[],erase177=True,retarget=-2,framework_states=118)
(base/args.output).write_text(json.dumps(report,indent=2)+'\n')
print({k:v for k,v in report.items()if k not in['rules','roots','routes']},flush=True)
