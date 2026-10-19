#!/usr/bin/env python3
"""Check a finite, explicit family of spare-count parity invariants.
This is not a lower bound and not a reachability proof for arbitrary CFG edges.
"""
import sys,json,collections
from pathlib import Path
HERE=Path(__file__).resolve().parent
D=HERE.parent/'context_folds/recovered/66'
sys.path.insert(0,str(D/'search/decoder'))
import explore as e
inv=json.loads((D/'results/interval-invariants.json').read_text())['invariants'];index={p:i for i,(p,_,_)in enumerate(e.SITES)}
def locate(P):
 edge,Q=e.rmpath.site(e.ORIGINAL,P);assert all(not b for b in P[len(Q):]);return index[''.join('1'if b else'0'for b in Q)]
edges=[]
for u,((pc,op,r),v)in enumerate(zip(e.SITES,inv)):
 if v is None or op=='CH':continue
 P=[b=='1'for b in pc]; nxt=[]
 if op=='CI':nxt=[(e.rmpath.inc_path(P),1^(1<<(r+1)),'increment')]
 elif op=='CD':
  if v[r][0]==0:nxt.append((e.rmpath.brk(1,P),1,'zero_decrement'))
  if v[r][1]>0:nxt.append((e.rmpath.inc_path(P),1<<(r+1),'positive_decrement'))
 elif op=='CB':nxt=[(e.rmpath.brk(r,P),0,'break')]
 elif op=='CC':nxt=[(e.rmpath.cont(r,P),0,'continue')]
 for pp,label,kind in nxt:edges.append(dict(source=u,target=locate(pp),label=label,kind=kind,register=r))
adj=collections.defaultdict(list)
for i,x in enumerate(edges):adj[x['source']].append((x['target'],i));adj[x['target']].append((x['source'],i))
pot={};parent={};constraints=[]
for root in sorted(adj):
 if root in pot:continue
 pot[root]=0;parent[root]=None;todo=collections.deque([root])
 while todo:
  u=todo.popleft()
  for v,k in adj[u]:
   if v not in pot:pot[v]=pot[u]^edges[k]['label'];parent[v]=(u,k);todo.append(v)
for k,x in enumerate(edges):
 expr=pot[x['source']]^pot[x['target']]^x['label']
 if expr:constraints.append(dict(edge=k,expression=expr))
basis={};contradiction=None
for i,c in enumerate(constraints):
 val=c['expression'];proof={i}
 for bit in range(9,0,-1):
  if val>>bit&1:
   if bit in basis:val^=basis[bit][0];proof^=basis[bit][1]
   else:basis[bit]=(val,proof);break
 else:
  if val==1:contradiction=sorted(proof);break
out=dict(status='NO_INVARIANT_IN_TESTED_FAMILY'if contradiction is not None else'LINEAR_FAMILY_SATISFIABLE',family='spare_count mod2 = node_potential(pc) XOR sum(c[r]*register[r] mod2), with nine fixed coefficient bits and arbitrary site potentials.',scope='All interval-admitted CFG transitions of the forward244 operation effects. These guarded edges are an overapproximation; this does not prove the same obstruction for the unique blank run or exclude nonlinear/history-dependent invariants.',nodes=len(pot),edges=len(edges),cycle_constraints=len(constraints),rank=len(basis),contradiction_constraints=contradiction,used_cycle_equations=[constraints[i]for i in contradiction]if contradiction else[],edges_certificate=edges,parent_certificate={str(k):v for k,v in parent.items()},potentials=pot,constraints=constraints)
(HERE/'spare_parity_audit.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items()if k not in['edges_certificate','parent_certificate','potentials','constraints']},indent=2))
