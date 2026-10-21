from pathlib import Path
import sys,json,time,collections
import numpy as np
from scipy.optimize import milp,Bounds,LinearConstraint
from scipy.sparse import lil_matrix
ROOT=Path(__file__).resolve().parents[1]
B=ROOT/'ProveIt/Computability/BusyBeaver/Research/ZFC'
D=ROOT/'reference_reports/K218_Dominated_Rho8_2026-10-20'
sys.path.insert(0,str(B/'k218-quantifier-stability/pricing'))
sys.path.insert(0,str(D/'binary/code/runtime'))
import source_language as s,build221 as b,independent_runtime as r
source=Path(sys.argv[1]);out=Path(sys.argv[2]);out.mkdir(exist_ok=True)
T=b.read_table((D/'binary/machine/k218.native.tm').read_bytes());oldrows=json.loads((D/'source/sites218.json').read_text());old=s.tree(oldrows);newrows=json.loads(source.read_text());new=s.tree(newrows)
groups,paths=b.decoder_map(T,old)
oldstates=collections.defaultdict(set)
for q,ns in groups.items():
 for n in ns:oldstates[n].add(q)
live=set()
def visit(n):
 if s.leaf(n)or n in live:return
 live.add(n);visit(n[0]);visit(n[1])
visit(new)
# Empirical protected-row census is only a synthesis filter. Every emitted
# candidate still requires a complete unbounded runtime proof and blank replay.
cache=ROOT/'root_work/dominated_phase_protected.json'
if cache.exists():protected={tuple(x)for x in json.loads(cache.read_text())}
else:
 protected=set()
 for i,site in enumerate(oldrows):
  p=site[0]
  for positive in ((False,True)if site[1]=='CD'else(False,)):
   regs=[1]*9
   if site[1]=='CD':regs[site[2]]=1 if positive else 0
   tape=r.frame(p,regs,[1]);q=84;h=0;phase=None;node=None;edgehead=None;child=None
   for tick in range(6000):
    if tick and(q==254 or(q==84 and r.clean_dispatch(96,h,tape))):break
    bit=int(h in tape);w,d,z=T[q,bit]
    if phase=='edge' and h==edgehead:phase='node';node=child
    if phase is None and q==84:phase='node';node=old
    if phase is None:protected.add((q,bit))
    elif phase=='node':
     ch=node[bit]
     if s.leaf(ch):phase=None
     else:phase='edge';edgehead=h+1;child=ch
    if w:tape.add(h)
    else:tape.discard(h)
    q=z;h+=d
   else:raise ValueError(('finite baseline failed',i,positive))
 cache.write_text(json.dumps(sorted(protected))+'\n')
 print('census rows',len(protected),flush=True)
# Exact local scanner replacement proved separately by complete contexts.
U={k:v for k,v in T.items()if k[0]!=50};U[34,0]=(1,-1,196);U[77,1]=(0,-1,75)
protected={k for k in protected if k[0]!=50}|{(34,0),(196,0),(196,1),(77,1)}
# Contextual decoder detours of retained subtrees use arithmetic/helper rows
# which cannot be recycled just because the detour is a decoder phase.
detourrows=set()
def detours(node,p,q):
 if s.leaf(node):return
 for bit,ch in enumerate(node):
  if s.leaf(ch):continue
  tape={i:int(c)for i,c in enumerate(p+str(bit))};tape[-1]=1;h=len(p);z=q
  for k in range(100):
   if h==len(p)+1:break
   v=tape[h];w,d,nxt=T[z,v]
   if k and node in live:detourrows.add((z,v))
   tape[h]=w;h+=d;z=nxt
  else:raise ValueError('old decoder detour does not close')
  detours(ch,p+str(bit),z)
detours(old,'',84);protected|=detourrows
mapped={n:min(qs)for n,qs in oldstates.items()if n in live and n!=new}
mapped[new]=84
occupied={q for q,ns in groups.items()if any(n in live for n in ns)}|{84};newnodes=[n for n in live if n not in mapped]
newnodes.sort(key=lambda n:repr(n))
pool=sorted({q for q,bit in U}-occupied)
# Always permit fresh states for a measured optimum, not just a yes/no failure.
pool+=list(range(500,510))
leafacts=collections.defaultdict(set)
for n,qs in oldstates.items():
 for bit,ch in enumerate(n):
  if s.leaf(ch):
   for q in qs:leafacts[ch,bit].add(T[q,bit])
leafacts[('CC',1),1].add((0,-1,1));leafacts[('CC',2),1].add((0,-1,16));leafacts[('CB',1),1].add((0,-1,40))
leafacts[('CI',5),1].add((1,1,63));leafacts[('CI',6),1].add((1,1,13))
# Fixed old-node mapping is permitted only while its child bindings remain old.
variables=[];dom={};implies=[]
for i,n in enumerate(newnodes):
 dom[i]=[]
 for q in pool:
  ok=True;req=[]
  for bit,ch in enumerate(n):
   if(q,bit)not in protected:continue
   action=U[q,bit]
   if s.leaf(ch):ok &= action in leafacts[ch,bit]
   elif action[:2]!=(bit,1):ok=False
   elif ch in mapped:ok &= action[2]==mapped[ch]
   else:req.append((ch,action[2]))
  if ok:
   j=len(variables);variables.append((i,q));dom[i].append(j);implies.append((j,req))
by={(newnodes[i],q):j for j,(i,q)in enumerate(variables)}
rows=[];lo=[];hi=[]
for i,js in dom.items():rows.append({j:1 for j in js});lo.append(1);hi.append(1)
for q in pool:
 js=[j for j,(i,z)in enumerate(variables)if q==z]
 if js:rows.append({j:1 for j in js});lo.append(0);hi.append(1)
for j,reqs in implies:
 for child,q in reqs:
  k=by.get((child,q))
  rows.append({j:1}if k is None else{j:1,k:-1});lo.append(-np.inf);hi.append(0)
# If a protected old/root row points into a reassigned new child, constrain it.
for n,q in mapped.items():
 for bit,ch in enumerate(n):
  if(q,bit)not in protected or s.leaf(ch)or ch in mapped:continue
  a=U[q,bit];j=by.get((ch,a[2]))if a[:2]==(bit,1)else None
  if j is None:rows.append({});lo.append(1);hi.append(1)
  else:rows.append({j:1});lo.append(1);hi.append(1)
A=lil_matrix((len(rows),len(variables)))
for i,row in enumerate(rows):
 for j,v in row.items():A[i,j]=v
c=np.array([0.0 if any((q,bit)in protected for bit in(0,1))else(1.0 if q<500 else 1.001)for i,q in variables])
started=time.monotonic();sol=milp(c=c,integrality=np.ones(len(c)),bounds=Bounds(0,1),constraints=LinearConstraint(A.tocsr(),lo,hi),options={'time_limit':30})
receipt=dict(source=str(source),source_metrics=s.metrics(new),new_roles=len(newnodes),pool=pool,protected_rows=len(protected),variables=len(c),constraints=len(rows),status=str(sol.message),seconds=time.monotonic()-started)
if sol.x is not None:
 for j,x in enumerate(sol.x):
  if x>.5:
   i,q=variables[j];mapped[newnodes[i]]=q
 for n,q in mapped.items():
  if n not in newnodes and n!=new:continue
  for bit,ch in enumerate(n):
   if(q,bit)in protected:continue
   if not s.leaf(ch):U[q,bit]=(bit,1,mapped[ch])
   else:
    acts=leafacts[ch,bit]
    direct=sorted(a for a in acts if a[:2]==(bit,1))
    if direct:U[q,bit]=direct[0]
    elif acts:U[q,bit]=sorted(acts)[0]
    else:raise ValueError(('No leaf action',ch,bit,q))
 reach={0};todo=[0]
 for q in todo:
  for bit in(0,1):
   z=U[q,bit][2]
   if z!=254 and z not in reach:reach.add(z);todo.append(z)
 U={k:v for k,v in U.items()if k[0]in reach}
 receipt.update(working_states=len(U)//2,allocations=[dict(state=mapped[n],node=repr(n))for n in newnodes],removed=sorted({q for q,bit in T}-reach))
 (out/'candidate.native.tm').write_bytes(b.table_bytes(U))
 try:
  g,_=b.decoder_map(U,new);receipt['decoder_status']='PASS'
  receipt['binding_failures']=[q for q,ns in g.items()for n in ns if mapped.get(n)!=q and q not in oldstates.get(n,set())]
 except Exception as e:receipt['decoder_status']=repr(e)
(out/'allocation.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:v for k,v in receipt.items()if k!='allocations'},indent=2),flush=True)
