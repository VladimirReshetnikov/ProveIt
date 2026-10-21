#!/usr/bin/env python3
import sys,json,collections,hashlib
from pathlib import Path
import numpy as np
from scipy.optimize import milp,LinearConstraint,Bounds
from scipy.sparse import lil_matrix
H=Path(__file__).resolve().parent;W=H.parent.parent
sys.path.insert(0,str(W/'encoding-work/upstream/candidate-k217/research/independent-helper-reconstruction'))
import source_language as s,build221 as b
PART=W/'upstream-late/extracted/K216_Partial_Selector_2026-10-20';PERM=W/'upstream-late/extracted/K216_Permuted_Commands_2026-10-21'
name=sys.argv[1]if len(sys.argv)>1 else'210'
T=b.read_table((PART/'machine/k216.native.tm').read_bytes());old=s.tree(json.loads((PART/'source/sites216.compact.json').read_bytes()));new=s.tree(json.loads((H/f'source{name}.json').read_bytes()))
G,P=b.decoder_map(T,old);oldstates=collections.defaultdict(set)
for q,nn in G.items():
 for n in nn:oldstates[n].add(q)
live=[];seen=set();paths={}
def walk(n,p=''):
 if s.leaf(n)or n in seen:return
 seen.add(n);live.append(n);paths[n]=p;walk(n[0],p+'0');walk(n[1],p+'1')
walk(new)
fixed={n:min(oldstates[n])for n in live if n in oldstates and n!=new}
fixedq=set(fixed.values())
pool=sorted(set(G)-fixedq-{0})
newnodes=[n for n in live if n not in fixed]
print('pool',pool,'newnodes',len(newnodes),'fixed',len(fixed),'fixedstates',len(fixedq))
# Known engine uses of retired decoder states. The row81 local equality makes92/1 free.
protected={(11,0),(26,0),(26,1),(37,0),(92,0),(213,0),(213,1)}
T[81,0]=(0,-1,111)
choices=collections.defaultdict(set)
for table,tree in [(T,old),(b.read_table((PERM/('machine/k216.native.tm'if name=='210'else'secondary/k216-120.native.tm')).read_bytes()),s.tree(json.loads((PERM/('machine/sites216.json'if name=='210'else'secondary/sites120.json')).read_bytes())))]:
 gg,_=b.decoder_map(table,tree)
 for q,nn in gg.items():
  for n in nn:
   for bit,ch in enumerate(n):
    if s.leaf(ch):choices[ch,bit].add(table[q,bit])
choices[('CC',1),1].add((0,-1,1));choices[('CC',2),1].add((0,-1,16));choices[('CB',1),1].add((0,-1,302))

def leafrow(ch,bit,q):
 opts=choices[ch,bit]
 if(q,bit)in protected:return T[q,bit]if T[q,bit]in opts else None
 if T[q,bit]in opts:return T[q,bit]
 direct=[r for r in opts if r[:2]==(bit,1)]
 if direct:return min(direct)
 if ch==('CC',1)and bit==1:return(0,-1,1)
 if ch==('CC',2)and bit==1:return(0,-1,16)
 if ch==('CB',1)and bit==1:return(0,-1,302)
 return min(opts)if opts else None

# Build the domains and conditional links needed by protected old rows.
dom={};links={}
for n in newnodes:
 for q in pool:
  if(n==new)!=(q==84):continue
  valid=True;needed=[]
  for bit,ch in enumerate(n):
   if s.leaf(ch):
    if leafrow(ch,bit,q)is None:valid=False
   elif(q,bit)in protected:
    w,d,z=T[q,bit]
    if(w,d)!=(bit,1):valid=False
    elif ch in fixed:
     if fixed[ch]!=z:valid=False
    elif z not in pool:valid=False
    else:needed.append((ch,z))
  if valid:dom[n,q]=len(dom);links[n,q]=needed
# Propagate unavailable conditional assignments.
while True:
 bad=[x for x in dom if any(y not in dom for y in links[x])]
 if not bad:break
 for x in bad:del dom[x]
dom={key:i for i,key in enumerate(dom)};constraints=[];lb=[];ub=[]
def row(v,l,u):constraints.append(v);lb.append(l);ub.append(u)
for n in newnodes:row({i:1 for(n0,q),i in dom.items()if n0==n},1,1)
for q in pool:row({i:1 for(n,q0),i in dom.items()if q0==q},0,1)
for x,i in dom.items():
 for y in links[x]:row({i:1,dom[y]:-1},-np.inf,0)
A=lil_matrix((len(constraints),len(dom)))
for r,values in enumerate(constraints):
 for col,v in values.items():A[r,col]=v
engineq={q for q,bit in protected}
c=np.array([-100 if q in engineq else 0 for n,q in dom],dtype=float)
res=milp(c,integrality=np.ones(len(dom)),bounds=Bounds(0,1),constraints=LinearConstraint(A.tocsr(),np.array(lb),np.array(ub)),options={'time_limit':30})
print('MILP',res.message,'vars',len(dom),'domains',[sum(n0==n for n0,q in dom)for n in newnodes])
if res.x is None:sys.exit(1)
assignment={n:q for(n,q),i in dom.items()if res.x[i]>.5};assert len(assignment)==len(newnodes);mapped=fixed|assignment
U=dict(T)
for n,q in assignment.items():
 for bit,ch in enumerate(n):U[q,bit]=leafrow(ch,bit,q)if s.leaf(ch)else(bit,1,mapped[ch])
for key in protected:assert U[key]==T[key]
reach={0};todo=[0]
for q in todo:
 for bit in(0,1):
  z=U[q,bit][2]
  if z!=254 and z not in reach:reach.add(z);todo.append(z)
U={k:v for k,v in U.items()if k[0]in reach}
errors=[]
try:
 gg,_=b.decoder_map(U,new)
 for q,nn in gg.items():
  for n in nn:
   expect=oldstates[n]if n in fixed else{mapped[n]}
   if q not in expect:errors.append([q,sorted(expect),paths.get(n)])
except Exception as ex:errors.append(str(ex))
print('PRICE',len(U)//2,'deleted',sorted(set(q for q,bit in T)-reach),'prefixerrors',errors)
records={'working_states':len(U)//2,'scope':'Exploratory constrained allocation, must pass full runtime and blank startup','source_metrics':s.metrics(new),'protected_rows':sorted(protected),'assignments':[{'q':q,'path':paths[n]}for n,q in assignment.items()],'prefix_errors':errors,'changes':[[q,bit,*row]for(q,bit),row in U.items()if T.get((q,bit))!=row]}
(H/f'constrained-{name}.native.tm').write_bytes(b.table_bytes(U));(H/f'constrained-{name}.json').write_text(json.dumps(records,indent=2)+'\n')
