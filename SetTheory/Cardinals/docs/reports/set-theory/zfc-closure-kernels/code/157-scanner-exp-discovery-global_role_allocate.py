"""Exploratory all-role allocation with an empirical fixed arithmetic engine.

Every source interior node may move. Ordinary decoder states are anonymous;
only fixed arithmetic states and their targets have identities in the MILP.
The output is a hypothesis, requiring independent full runtime/startup proofs.
"""
from pathlib import Path
import sys,json,collections,time
import numpy as np
from scipy.optimize import milp,Bounds,LinearConstraint
from scipy.sparse import lil_matrix
R=Path(__file__).resolve().parents[1];B=R/'ProveIt/Computability/BusyBeaver/Research/ZFC';D=R/'reference_reports/K218_Dominated_Rho8_2026-10-20'
sys.path.insert(0,str(B/'k218-quantifier-stability/pricing'))
import source_language as s,build221 as b
source=Path(sys.argv[1]);out=Path(sys.argv[2]);out.mkdir(exist_ok=True)
T=b.read_table((D/'binary/machine/k218.native.tm').read_bytes());old=s.tree(json.loads((D/'source/sites218.json').read_text()));new=s.tree(json.loads(source.read_text()));g,_=b.decoder_map(T,old)
P={tuple(x)for x in json.loads((R/'root_work/dominated_phase_protected.json').read_text())if x[0]!=50};T={k:v for k,v in T.items()if k[0]!=50};T[34,0]=(0,-1,75)
Q={q for q,bit in P};special=sorted(Q|{84});assert{T[k][2]for k in P}<=Q|{84,254}
nodes=set()
def visit(n):
 if s.leaf(n)or n in nodes:return
 nodes.add(n);visit(n[0]);visit(n[1])
visit(new);nodes=sorted(nodes,key=repr)
leafacts=collections.defaultdict(set)
for q,ns in g.items():
 for n in ns:
  for bit,ch in enumerate(n):
   if s.leaf(ch):leafacts[ch,bit].add(T[q,bit])
leafacts[('CC',1),1].add((0,-1,1));leafacts[('CC',2),1].add((0,-1,16));leafacts[('CB',1),1].add((0,-1,40));leafacts[('CI',5),1].add((1,1,63));leafacts[('CI',6),1].add((1,1,13))
V=[];dom={};reqs=[]
for i,n in enumerate(nodes):
 dom[i]=[]
 for q in ([84]if n==new else[None]+sorted(Q)):
  ok=True;req=[]
  if q is not None:
   for bit,ch in enumerate(n):
    if(q,bit)not in P:continue
    a=T[q,bit]
    if s.leaf(ch):ok &= a in leafacts[ch,bit]
    elif a[:2]!=(bit,1)or a[2]==84:ok=False
    else:req.append((ch,a[2]))
  if ok:j=len(V);V.append((i,q));dom[i].append(j);reqs.append((j,req))
by={(nodes[i],q):j for j,(i,q)in enumerate(V)};rows=[];lo=[];hi=[]
for i,js in dom.items():rows.append({j:1 for j in js});lo.append(1);hi.append(1)
for q in special:
 js=[j for j,(i,z)in enumerate(V)if q==z]
 if js:rows.append({j:1 for j in js});lo.append(0);hi.append(1)
for j,req in reqs:
 for child,q in req:
  k=by.get((child,q));rows.append({j:1}if k is None else{j:1,k:-1});lo.append(-np.inf);hi.append(0)
A=lil_matrix((len(rows),len(V)))
for i,row in enumerate(rows):
 for j,v in row.items():A[i,j]=v
c=np.array([1.0 if q is None else 0.0 for i,q in V]);t=time.monotonic();res=milp(c,integrality=np.ones(len(c)),bounds=Bounds(0,1),constraints=LinearConstraint(A.tocsr(),lo,hi),options={'time_limit':45})
rec=dict(source=str(source),metrics=s.metrics(new),interior_nodes=len(nodes),protected_rows=len(P),protected_states=len(Q),variables=len(V),constraints=len(rows),solver_status=str(res.message),seconds=time.monotonic()-t)
if res.x is not None:
 assign={nodes[i]:q for j,(i,q)in enumerate(V)if res.x[j]>.5};free=iter(sorted({q for q,bit in T}-Q-{84})+list(range(500,800)));generic=sum(q is None for q in assign.values())
 for n,q in list(assign.items()):
  if q is None:assign[n]=next(free)
 U={k:v for k,v in T.items()if k[0]in Q}
 for q in Q:
  for bit in(0,1):
   if(q,bit)not in P:U[q,bit]=(bit,-1,q)
 for n,q in assign.items():
  for bit,ch in enumerate(n):
   if(q,bit)in P:continue
   if not s.leaf(ch):U[q,bit]=(bit,1,assign[ch])
   else:
    acts=sorted(leafacts[ch,bit]);direct=[a for a in acts if a[:2]==(bit,1)]
    if not acts:raise ValueError(('missing leaf',ch,bit))
    U[q,bit]=(direct or acts)[0]
 rec.update(working_states=len(U)//2,generic_nodes=generic,engine_node_overlaps=len(nodes)-generic-1,objective=float(res.fun),mip_gap=float(res.mip_gap))
 (out/'candidate.native.tm').write_bytes(b.table_bytes(U))
 try:b.decoder_map(U,new);rec['decoder_status']='PASS'
 except Exception as e:rec['decoder_status']=repr(e)
 (out/'assignments.json').write_text(json.dumps([dict(state=q,node=repr(n))for n,q in assign.items()],indent=2)+'\n')
(out/'allocation.json').write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec,indent=2),flush=True)
