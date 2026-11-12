#!/usr/bin/env python3
"""Independent signed-root arithmetic and model premise review, no Lean."""
import hashlib,json,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b.decode()
s=pin('research/ordinary13-residue89-r-model-draft/Residue89RArithmetic.lean.src','be421b34e6701a194c3f68806a06099e373d2d64fba4bda9134fafd0460748aa')
pin('research/ordinary13-residue89-r-model-draft/receipt.json','bd4ee8b52dd71295f2b48a5f9d42da103b63269f62c38ccdc15ca7de548dacb3')
pin('reviews/ordinary13-natural-residue-forced89-independent/result.json','17b5fcebce8f734b68124b7ecfa477fec1f00ac73cadda915c29128fc27b1df8')
root=pin('Lean/DiophantineConsistency/Compact44/P72Root.lean','066fce52d35ab720519ee8817d9b56c2eacc9ac4f6bb7bf6e92286a87f44d091')
assert 'theorem ι_tsub' in root
for x in ['theorem r_positive_of_branches','(hPm : P<m)','(htP : t≤P)','(htau : ell<tau)','add_lt_add hprod htlt','theorem branches_of_signed_root','linear_combination hz-hs-hpcast','(hP : 1≤P) (hPt : P=b*t)','theorem tau_gt_ell','theorem P_below_m','(hK : K+1≤q^2)','(hC : C<q)','(hP : P+F=C*(X+K))']:
 assert x in s,x
# Check the two linear-combination signs in the free integer polynomial ring.
def v(n):return {(n,):1}
def add(a,b,k=1):
 d=a.copy()
 for t,c in b.items():d[t]=d.get(t,0)+k*c
 return {t:c for t,c in d.items() if c}
def mul(a,b):
 d={}
 for x,a0 in a.items():
  for y,b0 in b.items():
   t=tuple(sorted(x+y));d[t]=d.get(t,0)+a0*b0
 return {t:c for t,c in d.items() if c}
one={():1};b,P,t,ell,k,tau,z=map(v,['b','P','t','ell','k','tau','z'])
hz=add(add(z,mul(b,add(add(ell,k),mul(k,P),-1)),-1),P)
hp=add(P,mul(b,t),-1)
for sign in (1,-1):
 hs=add(z,mul(b,tau),-sign)
 cert=add(add(hz,hs,-1),hp,-1)
 expected=mul(b,add(add(add(mul(k,add(P,one,-1)),t),ell,-1),tau,sign))
 assert cert==expected
# Strict comparison and K-bound size cut: finite controls, never a replacement for proof.
for m in range(2,35):
 for P0 in range(1,m):
  for t0 in range(1,P0+1):
   for k0 in range(2,9):
    ell0=m*k0
    assert k0*(P0-1)<ell0 and t0<ell0 and k0*(P0-1)+t0<2*ell0
assert 2*(99-1)+99>2*99
for q in range(2,8):
 for X in range(1,5):
  for K in range(q*q):
   for C in range(q):
    for F in range(1,4):
     P0=C*(X+K)-F
     if P0>=0:
      Y=q**3;assert P0<q*(X+K)<=X*q*(K+1)<=X*q**3<=X*Y*Y
print(json.dumps({'scope':'exact signed branch certificates and bounded arithmetic controls; no Lean','branch_signs_verified':True,'corrected_two_ell_bound':True,'represented_K_plus_one_le_q_squared_required':True,'signed_graph_and_quotient_facts_are_premises':True,'lean_elaborated':False},sort_keys=True,indent=2))
