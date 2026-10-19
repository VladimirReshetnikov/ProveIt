#!/usr/bin/env python3
"""Finite algebraic identities used by colored_model_addendum.tex.

Checks every truth-valued two-point GIC fiber and every pair of finite
truth vectors. Does not claim to construct a model of ZFC.
"""
from itertools import product
import json

M=[[3,3,3,3],[3,3,0,3],[3,3,3,3],[0,0,0,3]]
order=[0,2,1,3]
rank={x:i for i,x in enumerate(order)}
C=lambda a,b:M[a][b]
N=lambda a:C(a,0)
Q=lambda seq:min(seq,key=rank.__getitem__)
E=lambda seq:N(Q([N(x) for x in seq]))
A=lambda a,b:N(C(a,N(b)))

def main():
  if not __debug__:
    raise RuntimeError("Run with assertions enabled; do not use -O or -OO")
  for a,b in product(range(4),repeat=2):
    assert A(a,b) in (0,3) and (A(a,b)==3)==(a==b==3)
    if b in (0,3):assert (C(a,b)==3)==(a!=3 or b==3)
  vectors=list(product(range(4),repeat=2))
  for p in vectors:
    assert E(p) in (0,3) and (E(p)==3)==any(x==3 for x in p)
    assert (Q(p)==3)==all(x==3 for x in p)
  # Pointwise designated implication is closed under the quantifier meet.
  for p,q in product(vectors,repeat=2):
    if all(C(a,b)==3 for a,b in zip(p,q)):
      assert C(Q(p),Q(q))==3
  count=0
  for domain,collection in product(vectors,repeat=2):
    for cells in product(range(4),repeat=4):
      phi=[cells[:2],cells[2:]]
      cover=Q([C(domain[x],Q([C(phi[x][y],E([A(phi[x][z],collection[z]) for z in range(2)])) for y in range(2)])) for x in range(2)])
      support=Q([C(collection[y],E([phi[x][y] for x in range(2)])) for y in range(2)])
      actual=A(cover,support)==3
      expected=all(domain[x]!=3 or not any(phi[x][y]==3 for y in range(2)) or any(phi[x][y]==3 and collection[y]==3 for y in range(2)) for x in range(2)) and all(collection[y]!=3 or any(phi[x][y]==3 for x in range(2)) for y in range(2))
      assert actual==expected,(domain,collection,cells)
      count+=1
  print(json.dumps({"status":"PASS","GIC_two_point_cases":count,"meet_closure_pairs":len(vectors)**2,"scope":"Finite value identities only; ordinary model argument is in colored_model_addendum.tex."},indent=2))

if __name__=='__main__':main()
