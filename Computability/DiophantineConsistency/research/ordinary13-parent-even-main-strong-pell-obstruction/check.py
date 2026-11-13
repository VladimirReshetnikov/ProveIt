#!/usr/bin/env python3
"""Bounded independent controls for the all-even-index Pell obstruction."""
import hashlib,json,math
from pathlib import Path
root=Path(__file__).resolve().parents[2];here=Path(__file__).resolve().parent
for p,h in json.loads((here/'pins.json').read_text()).items():assert hashlib.sha256((root/p).read_bytes()).hexdigest()==h,p
parent=json.loads((root/'research/ordinary13-eta-zero-graph-adapter-audit/prototype.json').read_text())
r={x[0]:x[1:] for x in parent['source']}
exp={'f2':['*','n_f','n_f'],'rho':['-','f2',1], 'Q':['*','Delta','rho'],
 'I':['*','c2','i'],'g72':['-','g71','Q'],'g74':['*','T','c'],
 'g75':['-','g74','R'],'g76':['*','f2','g75'],'V':['-','g76','c'],
 'y2':['*','n_y','n_y'],'Fa':['-','y2','g82'],
 'i':['+','n_i',1],'T':['+','n_T',1]}
for k,v in exp.items():assert r[k]==v,(k,r[k])
rec=(root/'Lean/DiophantineConsistency/ArithmeticPellRecurrence.lean').read_text()
for x in ('xcoord (time+1) b=(b+2)*xcoord time b+delta b*ycoord time b',
          'ycoord (time+1) b=xcoord time b+(b+2)*ycoord time b'):assert x in rec
primes=[p for p in range(3,100,2) if all(p%d for d in range(2,math.isqrt(p)+1))]
def pell(A,n,mod=None):
 D=A*A-1;x,y=1,0
 for _ in range(n):
  x,y=A*x+D*y,x+A*y
  if mod:x%=mod;y%=mod
 return x,y
for A in range(2,18):
 for j in range(25):assert pell(A,j,2)[1]==j%2
prime_cases=0
for A in range(2,18):
 for h in range(2,14,2):
  for p in primes:
   x,v=pell(A,h,p)
   if x==0:
    assert v!=0 and ((A*A-1)*v*v+1)%p==0
    for j in range(1,100,2):assert pell(A,j,p)[1]!=0
    prime_cases+=1
# Integer Lucas identity, including negative differences.
def ordinate(A,j):return -pell(A,-j)[1] if j<0 else pell(A,j)[1]
identities=0
for A in range(2,9):
 for m in range(2,14,2):
  for ell in range(1,14,2):
   assert ordinate(A,ell)**2-ordinate(A,m)**2==ordinate(A,ell-m)*ordinate(A,ell+m)
   identities+=1
# Concrete bounded arithmetic control; it is not a graph zero.
A=2;m=2;h=8;p=31;f,v=pell(A,h);_,c=pell(A,m);D=A*A-1
assert (f,v,c)==(18817,10864,4) and f%p==0 and v%(c*c)==0
I=D*v;assert I*I==D*(f*f-1) and I%p!=0
coeff=(4*(I*I%p)-2)%p;v0=1;v1=(4*(I*I%p)-3)%p
seq=[]
for _ in range(16):seq.append(v0);v0,v1=v1,(coeff*v1-v0)%p
assert (v0,v1)==(1,(4*(I*I%p)-3)%p)
assert c%p not in seq and (-c)%p not in seq
print(json.dumps({'actual_parent_rows_checked':len(exp),'bounded_odd_prime_even_h_cases':prime_cases,
 'Lucas_identity_controls_including_negative_indices':identities,
 'concrete_toy_A_m_h_f_prime':[A,m,h,f,p],
 'odd_auxiliary_quotient_residues_mod_prime':sorted(set(seq)),
 'Pell_ordinate_parity_for_even_and_odd_multiplier_checked':True,
 'same_strong_family_even_main_parent_completion_impossible':True,
 'other_strong_witness_or_changed_two_norm_excluded':False,
 'actual_full_graph_zero_constructed':False,'lean_executed':False},indent=2,sort_keys=True))
