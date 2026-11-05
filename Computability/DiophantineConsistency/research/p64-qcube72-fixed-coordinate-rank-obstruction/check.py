#!/usr/bin/env python3
"""Finite controls for fixed-coordinate rank congruence, not a proof search."""
import hashlib,json,math,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B without optimization')
r=Path(__file__).resolve().parents[2]
pins={r/'research/p64-qcube72-full-zero-mod-q-obstruction/README.md':'99b0da7530b0f7bbbaed76fd8c452b9791280babba8d8f2f82573552b842a860',r/'research/p64-qcube72-full-zero-mod-q-obstruction/check.py':'a6e1d4ad04e290865a603c4de1a2ff2a3819f44b27d530fc1bdf8ff005ead435',r/'research/p64-qcube72-free-main-candidate/graph.json':'875a9d0972c350e6858e25b68f2dc794b1f330e61f29cd52a5853ece90b24806',r/'Lean/DiophantineConsistency/Compact44/CompactSymbolicPorts.lean':'0fc8eb4f60e801b38a3a516cd23d9f44c1e9eda62609d34bd76764de7ac51414',r/'Lean/DiophantineConsistency/Compact44/CompactFixedBeta.lean':'bcb892e7ae6b0d3cf329a248ca6b468e36a9a1b582d75cacafb7fd49f89025ea'}
for p,h in pins.items():
    if hashlib.sha256(p.read_bytes()).hexdigest()!=h:raise RuntimeError('input drift '+str(p))
cases=0;rigid=0
for beta in range(1,7):
 for J in range(1,5):
  q=beta*J+1;B=q-1
  for F in range(1,q-1):
   for alpha in range(1,q-F):
    C=q-F-alpha
    for MC in range(6):
     R=(B*(q-F)+alpha)*(q*q-1)+(MC+q*3)*J
     if (R-C-MC*J)%q:raise RuntimeError('rank congruence')
     # Any positive new F,alpha at the same C and F modulo B is identical.
     for j in (-2,-1,0,1,2):
      FF=F+B*j;aa=alpha-B*j
      if FF>0 and aa>0:
       if j!=0:raise RuntimeError('fixed-C non-rigidity')
       rigid+=1
     cases+=1
# If U divides H*h, the q^3 scale forces q divides h. Test the
# minimal such h=U/gcd(U,H) for a bounded exhaustive family.
divisibility_cases=0
for q0 in range(3,50):
 for scale in range(1,8):
  Y=q0**3*scale; U=Y*Y
  for x in range(1,8):
   a=(x+1)*Y; H=4*a+3
   gap=U//math.gcd(U,H)
   if gap%q0:raise RuntimeError('q does not divide minimal gap')
   divisibility_cases+=1
# Counterexample to omitting the w-fixed condition: both transport
# equations hold at q=5, C=1, K0=1, yet F differs modulo q-1.
qtest=5;Ktest=1;Ctest=1
for Ftest,atest,wtest,ztest in ((1,3,4,1),(2,2,5,1)):
 if qtest-Ftest-atest!=Ctest or (Ktest+wtest)*Ctest!=Ftest+ztest*(qtest-1):raise RuntimeError('transport control')
if (2-1)%(qtest-1)==0:raise RuntimeError('counterexample not discriminating')
# Full-zero packet's residues, ports and target C. c≡115 mod729, m≡184.
q=3;J=1;h=486%q;k=428%q;c=115%q;m=184%q;MC=(m-40+c)%q
wanted=(h+k-1-MC*J)%q
if (h,k,c,m,MC,wanted)!=(0,2,1,1,1,0):raise RuntimeError('full-zero target mismatch')
print(json.dumps({'status':'PASS_FINITE_CONTROLS','rank_cases':cases,'divisibility_cases':divisibility_cases,'positive_fixed_C_cases':rigid,'unfixed_w_negative_control':True,'symbolic_zero_q':q,'symbolic_zero_target_C_mod_q':wanted,'scope':'Finite checks only; universal modular and interval arguments are mathematical and do not settle compact44 existence.'},sort_keys=True))
