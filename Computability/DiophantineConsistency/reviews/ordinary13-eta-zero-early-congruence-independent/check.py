#!/usr/bin/env python3
"""Independent read-only source pins, free-ring and finite number controls."""
import json, hashlib, math
from pathlib import Path
HERE=Path(__file__).resolve().parent; ROOT=HERE.parents[1]
pins=json.loads((HERE/'pins.json').read_text())
for p,h in pins.items(): assert hashlib.sha256((ROOT/p).read_bytes()).hexdigest()==h,p
N=9
class P:
 def __init__(self,t): self.t={m:c for m,c in t.items() if c}
 def __add__(self,o):
  o=L(o); d=dict(self.t)
  for m,c in o.t.items():d[m]=d.get(m,0)+c
  return P(d)
 __radd__=__add__
 def __neg__(self):return P({m:-c for m,c in self.t.items()})
 def __sub__(self,o):return self+-L(o)
 def __rsub__(self,o):return L(o)+-self
 def __mul__(self,o):
  o=L(o); d={}
  for m,c in self.t.items():
   for n,e in o.t.items():
    k=tuple(x+y for x,y in zip(m,n));d[k]=d.get(k,0)+c*e
  return P(d)
 __rmul__=__mul__
 def __eq__(self,o):return self.t==L(o).t
def L(n):return n if isinstance(n,P) else P({(0,)*N:n})
def var(i):return P({tuple(int(j==i) for j in range(N)):1})
q,X,s,k,R,c,gamma,main,Y0=map(var,range(N));Y=q*q*q*s;U=Y*q*q;a=X*Y+Y;H=3+4*a
assert U==q*q*q*q*q*s
car=U*main+H*k-U*(X+a*c)-H*(U*gamma+R+1)
congruence=H*(R+1)+q*q*q*q*q*(s*(X+a*c+H*gamma))-H*k-q*q*q*q*q*(s*main)
assert car == -congruence
assert H == 3+4*Y*(X+1)
# Finite arithmetic controls for the factor-three step, including q=1 and s=0.
# They do not prove the imported model theorem.
tested=0; divisible3=0
for n in range(1,101):
 for x in range(7):
  for st in range(5):
   yy=n**3*st; hh=3+4*yy*(x+1); d=math.gcd(n**5,hh)
   assert n%d==0
   assert (n**5//d)%(n**4)==0
   tested+=1; divisible3+=n%3==0
p=json.loads((ROOT/'research/ordinary13-eta-zero-graph-adapter-audit/prototype.json').read_text()); rows={r[0]:r[1:] for r in p['source']}
for name,row in {'r0':['-','kbase','R'],'g54':['*','U','n_gamma'],'shift':['-','g54','r0'],'g58':['*','U','b0'],'g59':['*','H','shift'],'Dstar':['+','g58','g59'],'k':['+','kbase',1]}.items():assert rows[name]==row
print(json.dumps({'source_pins':pins,'balance_and_coefficient_free_ring_identities':True,
 'factor_three_finite_controls':tested,'controls_with_three_dividing_q':divisible3,
 'lean_executed':False,'status':'bounded source audit; model imports and all graph premises remain unelaborated'},sort_keys=True,indent=2))
