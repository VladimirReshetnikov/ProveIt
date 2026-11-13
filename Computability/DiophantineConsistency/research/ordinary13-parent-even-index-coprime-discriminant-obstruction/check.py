#!/usr/bin/env python3
"""Bounded arithmetic controls for the all-discriminants same-data theorem."""
import hashlib,json,math,subprocess,sys
from pathlib import Path
root=Path(__file__).resolve().parents[2];here=Path(__file__).resolve().parent
for p,h in json.loads((here/'pins.json').read_text()).items():assert hashlib.sha256((root/p).read_bytes()).hexdigest()==h,p
prev=root/'research/ordinary13-parent-even-index-squarefree-same-data-obstruction'
r=subprocess.run([sys.executable,'-I','-S','-B',str(prev/'check.py')],cwd=root,check=True,text=True,capture_output=True)
assert r.stdout==(prev/'receipt.json').read_text()
# Exact fundamental-unit Pell arithmetic, with ordinary integer arithmetic.
def pell(d,a,b,n,mod=None):
 def mul(x,y):
  z=(x[0]*y[0]+d*x[1]*y[1],x[0]*y[1]+x[1]*y[0])
  return tuple(t%mod for t in z) if mod else z
 out=(1,0);unit=(a,b)
 while n:
  if n&1:out=mul(out,unit)
  unit=mul(unit,unit);n//=2
 return out
units=[(2,3,2),(3,2,1),(5,9,4),(6,5,2),(7,8,3),(10,19,6),(11,10,3),(15,4,1)]
count=0
for d,a,b in units:
 assert a*a-d*b*b==1
 seq=[pell(d,a,b,j)[1] for j in range(17)]
 for j in range(1,17):
  for k in range(1,17):
   assert math.gcd(seq[j],seq[k])==seq[math.gcd(j,k)]
   count+=1
# Independently check valuation lemma Δ=d*t² | I² => d*t | I over a bounded range.
for d in (2,3,5,6,7,10,11,13,15):
 for t in range(1,15):
  D=d*t*t
  for I in range(1,180):
   if I*I%D==0:assert I%(d*t)==0
# A concrete non-squarefree, non-fundamental main multiplier: (8+3√7)^3=2024+765√7.
d=7;a,b=8,3;ridx=3;A,t=pell(d,a,b,ridx)
assert (A,t)==(2024,765)
D=A*A-1;assert D==d*t*t and D%(3*3)==0
m=2;_,c=pell(D,A,1,m)
assert c==4048 and math.gcd(m,D)==math.gcd(c,D)==1
rm=ridx*m;_,u=pell(d,a,b,rm)
assert u==t*c
_,uhalf=pell(d,a,b,rm//2);assert c>uhalf
# This symbolic strong witness is in the A-Pell family at j=4A;
# check c²|u_h by modular powering, never expand its huge f.
h=ridx*4*A;assert h%rm==0
_,uh=pell(d,a,b,h,mod=c*c);assert uh==0
for h0 in range(1,61):
 _,uh0=pell(d,a,b,h0,mod=c)
 if uh0==0:assert h0%rm==0
print(json.dumps({'inherited_even_family_obstruction_reproduced':True,
 'pell_ordinate_gcd_controls':count,'squarefree_kernel_valuation_controls':True,
 'nonsquarefree_example':{'A':A,'Delta':D,'kernel':d,'t':t,'unit_r':ridx,'m':m,'c':c},
 'nonfundamental_main_unit_modular_control':True,
 'conditional_same_data_parent_completion_excluded':True,
 'actual_compact_zero_or_existential_inequivalence_proved':False,
 'lean_executed':False},indent=2,sort_keys=True))
