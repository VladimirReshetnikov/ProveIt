#!/usr/bin/env python3
"""Independent parent-to-88 natural guard source review; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary13-parent-to-88-guard-draft'
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,str(p);return b
s=pin(A/'ParentTo88Guard.lean','f247f608bbfe1d09e66e50e98bd90d7fc02b4dbef20cf0d2371d31e571719de7').decode()
pin(A/'check_source.py','530cb0086ff7bf8da7c5f35e342fc6415cc36cbe3474fd4787903dc4f041ecba')
receipt=pin(A/'observation.json','87d30b4f4a842c2ce61e03f0e4989273b5c637d81ca0c48b2ff9f4d7c995896f')
r=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary13-parent-to-88-guard-draft-independent/`.\n')
assert r.endswith(tail) and sha(r[:-len(tail)])=='d3114b126de353a21c556201a5598b3d83f7451f19559d1b04d7f9b62000f0e1'
for name,ch,rh in (
 ('ordinary13-parent-to-88-ring-client-draft-independent','a9da9ee6a83c8e427fce9bc1ffd31ffbae0d90838621e73ec90abd7efd2fa3b6','93c66ee81872d59375690e60fb40f02ac1582363bde2e0c02ff11e051cca1996'),
 ('ordinary13-parent-transport-quotients-draft-independent','2fcfaebf6fbb2df8aabac391b2185045526e2330c23f2ffa7e237149968e9d38','6cb501f7c88bc31a170da8157dcbf08f178f12da66025bfbc81be53b400c8d69')):
 p=D/'reviews'/name;pin(p/'check.py',ch);pin(p/'result.json',rh)
for f in ('q*A=(v 1+v 2)*A+v 1*q+b*t','P72Root.cast_port p 0','P72Root.cast_port p 1',
 'rw [bt_eval,b_eval,hp0,hp1]','linear_combination h'):
 assert f in s,f
assert 'linear_combination -h' not in s
# Exact polynomial: target guard equals the left-minus-right transport balance.
def plus(a,b):
 c=a.copy()
 for k,v in b.items():c[k]=c.get(k,0)+v
 return {k:v for k,v in c.items() if v}
def neg(a):return {k:-v for k,v in a.items()}
def mul(a,b):
 c={}
 for x,u in a.items():
  for y,v in b.items():
   z=tuple(i+j for i,j in zip(x,y));c[z]=c.get(z,0)+u*v
 return {k:v for k,v in c.items() if v}
one={(0,)*6:1};b,F,alpha,K,X,t=({tuple(int(i==j) for i in range(6)):1} for j in range(6))
q=plus(one,b);AA=plus(X,mul(K,q))
guard=plus(plus(mul(plus(plus(q,neg(F)),neg(alpha)),AA),neg(mul(F,q))),neg(mul(b,t)))
balance=plus(mul(q,AA),neg(plus(plus(mul(plus(F,alpha),AA),mul(F,q)),mul(b,t))))
assert guard==balance
rr=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
assert not rr.stderr and rr.stdout==receipt
print(json.dumps({'scope':'parent-to-88 natural guard source review; no Lean','exact_balance_orientation':'guard equals left-minus-right','prior_component_reviews':'pinned, not rerun'},sort_keys=True,indent=2))
