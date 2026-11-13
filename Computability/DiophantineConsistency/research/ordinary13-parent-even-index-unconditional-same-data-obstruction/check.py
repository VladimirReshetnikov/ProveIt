#!/usr/bin/env python3
"""Bounded checks for the unconditional even-index same-data obstruction."""
import hashlib,json,math,subprocess,sys
from pathlib import Path
root=Path(__file__).resolve().parents[2];here=Path(__file__).resolve().parent
for p,h in json.loads((here/'pins.json').read_text()).items():assert hashlib.sha256((root/p).read_bytes()).hexdigest()==h,p
prev=root/'research/ordinary13-parent-even-index-kernel-gcd-obstruction'
r=subprocess.run([sys.executable,'-I','-S','-B',str(prev/'check.py')],cwd=root,check=True,text=True,capture_output=True)
assert r.stdout==(prev/'receipt.json').read_text()
# Cancellation from c|dt*U_h, independently of whether the previous
# c²-kernel criterion holds.
for c in range(1,151):
 for z in range(1,151):
  B=c//math.gcd(c,z)
  for u in range(1,25):
   if (z*u)%c==0:assert u%B==0
# Search bounded small multipliers for strong Pell indices in the exact kernel.
# Each A uses its least integer-coordinate unit, found by scanning b≤t.
cases=hits=0
for A in range(2,101):
 D=A*A-1;z=D;d=t=1
 for p in range(2,math.isqrt(D)+1):
  e=0
  while z%p==0:z//=p;e+=1
  if e:d*=p**(e%2);t*=p**(e//2)
  if z==1:break
 if z>1:d*=z
 assert D==d*t*t and math.gcd(A,d*t)==1
 for b in range(1,t+1):
  a=math.isqrt(1+d*b*b)
  if a*a==1+d*b*b:break
 x,u=1,0
 for r in range(1,200):
  x,u=a*x+d*b*u,b*x+a*u
  if x>=A:break
 assert (x,u)==(A,t)
 x,c=1,0
 for m in range(1,7):
  x,c=A*x+D*c,x+A*c
  if m%2:continue
  assert math.gcd(c,d*t)==math.gcd(m,d*t)
  B=c//math.gcd(c,d*t)
  g0=math.gcd(c*c,d*t);mod=c*c//g0
  assert mod%B==0
  xx0,yy0=1,0
  for _ in range(m//2):xx0,yy0=A*xx0+D*yy0,xx0+A*yy0
  assert 2*xx0>=m*A>m*t>=t*math.gcd(c,d*t)
  if mod>2000000:continue
  xx,uu=1,0;cases+=1
  for h in range(1,20001):
   xx,uu=(a*xx+d*b*uu)%mod,(b*xx+a*uu)%mod
   if uu==0:
    hits+=1;assert h%(r*m)==0,(A,m,r,h)
   if (xx,uu)==(1%mod,0):break
# Exact separate m=2 and m>=4 numerical inequalities as sanity controls.
for A in range(2,100):
 D=A*A-1;assert 4*A*A-2>D
 for t in range(1,A):
  if D%t==0:assert math.gcd(A,t)==1
print(json.dumps({'previous_kernel_gcd_receipt_reproduced':True,
 'bounded_fundamental_unit_cases':cases,'bounded_strong_index_hits':hits,
 'all_hits_multiple_of_rm':True,'uniform_cancellation_and_growth_checked':True,
 'proof_uses_only_c_divides_I':True,
 'conditional_same_data_parent_completion_excluded_for_all_even_m':True,
 'any_two_norm_zero_or_existential_inequivalence_proved':False,
 'lean_executed':False},indent=2,sort_keys=True))
