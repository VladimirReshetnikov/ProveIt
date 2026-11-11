#!/usr/bin/env python3
"""Exact polynomial identity, mod-4 cases, and gate count; no Lean."""
import hashlib,itertools,json
from pathlib import Path
root=Path(__file__).resolve().parents[2]
p=root/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json'
data=p.read_bytes()
assert hashlib.sha256(data).hexdigest()=='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e'
g=json.loads(data); rows=g['source']
assert len(rows)==65 and rows[23]==['N1','-','main_square','Dc2']
assert rows[33]==['R','+','rproduct','mask']
assert rows[36]==['tau','-','tau_partial','R'] and rows[48]==['cTminusR','-','cT','R']
assert sum(x=='R' for row in rows[34:] for x in row[2:])==2
new=rows[:34]+[['rank_plus_main','+','R','N1'],['sheared_rank','-','rank_plus_main',1]]
new += [[row[0],row[1],*['sheared_rank' if x=='R' else x for x in row[2:]]] for row in rows[34:]]
def live(rs):
 e={r[0]:r[2:] for r in rs}; seen=set(); todo=[g['output']]
 while todo:
  v=todo.pop()
  if v in e and v not in seen: seen.add(v);todo.extend(e[v])
 return len(seen)
assert live(rows)==65 and live(new)==67
assert all((d*d-((a+2)**2-1)*c*c)%4!=3 for a,c,d in itertools.product(range(4),repeat=3))
# Sparse polynomials in Q,tau,N0,Na,S2,V,f2,Nt,Z.
n=9;zero=(0,)*n
def lit(k): return {} if not k else {zero:k}
def var(i): return {tuple(int(j==i) for j in range(n)):1}
def add(a,b):
 c=a.copy()
 for m,k in b.items():
  c[m]=c.get(m,0)+k
  if not c[m]: del c[m]
 return c
def neg(a): return {m:-k for m,k in a.items()}
def sub(a,b): return add(a,neg(b))
def mul(a,b):
 c={}
 for x,u in a.items():
  for y,v in b.items():
   m=tuple(p+q for p,q in zip(x,y));c[m]=c.get(m,0)+u*v
 return {m:k for m,k in c.items() if k}
def prod(*items):
 o=lit(1)
 for x in items:o=mul(o,x)
 return o
Q,tau,N0,Na,S2,V,f2,Nt,Z=map(var,range(n)); d=sub(Q,lit(1))
N0p=add(N0,add(neg(prod(lit(2),tau,d)),mul(d,d)))
Nap=add(Na,prod(S2,add(neg(prod(lit(2),V,f2,d)),prod(f2,f2,d,d))))
left=prod(Q,Nt,Z,sub(prod(N0p,Nap),prod(N0,Na)))
bracket=add(prod(add(neg(prod(lit(2),tau)),d),Nap),prod(N0,S2,add(neg(prod(lit(2),V,f2)),prod(f2,f2,d))))
assert left==prod(Q,Nt,Z,d,bracket)
print(json.dumps({'graph_sha256':hashlib.sha256(data).hexdigest(),'original_live_gates':live(rows),'sheared_live_gates':live(new),'mod4_cases':64,'exact_sparse_polynomial_identity':True},sort_keys=True,indent=2))
