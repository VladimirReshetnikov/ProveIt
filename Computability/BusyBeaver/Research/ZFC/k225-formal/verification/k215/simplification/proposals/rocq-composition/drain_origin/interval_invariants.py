"""Owned sound finite interval abstraction for every arbitrary initial register file."""
if not __debug__:
 raise SystemExit("Verification requires assertions: do not use -O or PYTHONOPTIMIZE.")
from pathlib import Path
import json,collections
B=Path(__file__).resolve().parent;G={int(k):v for k,v in json.loads((B/'input_graph.json').read_text()).items()}
CAP=8;INF=CAP+1
TOP=tuple((0,INF) for _ in range(9))
def join(a,b):
 if a is None:return b
 return tuple((min(l,x),max(h,y)) for (l,h),(x,y) in zip(a,b))
def edge(I,r,branch,incs):
 l,h=I[r];out=list(I)
 if branch==0: # nonzero: decrement then increments
  if h==0:return None
  out[r]=(max(0,l-1), h-1 if h<INF else INF)
 else:
  if l>0:return None
  out[r]=(0,0)
 for i,k in incs:
  l,h=out[i];out[i]=(min(CAP,l+k),min(INF,h+k))
 return tuple(out)
Inv={v:None for v in G};Inv[0]=TOP;q=collections.deque([0]);iters=0
while q:
 v=q.popleft();iters+=1;x=G[v]
 if x['op'][0]=='halt':continue
 r=x['op'][1]
 for b,(t,incs) in enumerate(x['successors']):
  J=edge(Inv[v],r,b,incs)
  if J is not None:
   K=join(Inv[t],J)
   if K!=Inv[t]:Inv[t]=K;q.append(t)
# A separate full inductiveness check is the certificate verification condition.
assert Inv[0]==TOP
for v,x in G.items():
 if Inv[v] is None or x['op'][0]=='halt':continue
 for b,(t,incs) in enumerate(x['successors']):
  J=edge(Inv[v],x['op'][1],b,incs)
  if J is not None:
   assert Inv[t] is not None and all(l<=x and y<=h for (l,h),(x,y) in zip(Inv[t],J))
forced=[]
for v,x in G.items():
 if Inv[v] is None or x['op'][0]=='halt':continue
 r=x['op'][1];l,h=Inv[v][r]
 if h==0:forced.append({'vertex':v,'register':r,'taken_branch':'zero','interval':[l,h]})
 elif l>0:forced.append({'vertex':v,'register':r,'taken_branch':'nonzero','interval':[l,h]})
res={'vertices':len(G),'reachable_under_intervals':sum(i is not None for i in Inv.values()),'forced_tests':len(forced),'forced_zero':sum(x['taken_branch']=='zero' for x in forced),'forced_nonzero':sum(x['taken_branch']=='nonzero' for x in forced),'iterations':iters,'inductive_certificate_checked':True,'initial_register_domain':'all nine natural registers arbitrary','cap':CAP,'infinity_sentinel':INF,'scope':'Finite Python abstract-interpretation certificate check, not a formal proof assistant result.'}
(B/'INTERVAL_AUDIT.json').write_text(json.dumps(res,indent=2)+'\n');(B/'invariants.json').write_text(json.dumps(Inv));(B/'forced_tests.json').write_text(json.dumps(forced,indent=2));print(json.dumps(res,indent=2))
