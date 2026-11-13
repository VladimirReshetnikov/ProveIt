#!/usr/bin/env python3
"""Exact bounded and source-pinned checks for the w=1 consequences."""
import hashlib,json,math
from pathlib import Path
root=Path(__file__).resolve().parents[2];here=Path(__file__).resolve().parent
for name,digest in json.loads((here/'pins.json').read_text()).items():
 assert hashlib.sha256((root/name).read_bytes()).hexdigest()==digest,name
beta_src=(root/'Lean/DiophantineConsistency/Compact44/CompactFixedBeta.lean').read_text()
assert 'def betaNat : ℕ := 2^(67*8807)-1' in beta_src
mask=(root/'Lean/DiophantineConsistency/Compact44/CompactConcreteMask.lean').read_text()
assert 'range 943 ∪ Ico 983 993' in mask
ls=(root/'Lean/DiophantineConsistency/Compact44/CompactListMask.lean').read_text()
assert 'if j=special then B-4 else if j∈S then B-2 else B-1' in ls
rows={x[0]:x[1:] for x in json.loads((root/'research/ordinary13-eta85-shift-boundary-probes/F-probe.json').read_text())['source']}
for k,v in {'q':['+',1,'qm'],'X':['*','q','n_w'],'Y':['*','q3','s'],
 'U':['*','Y','q2'],'C':['-','qF','alpha'],'G':['+','alpha','g44'],
 'R':['+','g47','g50'],'r0':['-','kbase','R'],'shift':['-','g54','r0'],
 'Dstar':['+','g58','g59']}.items():assert rows[k]==v
N=67*8807; assert N==590069 and N%2==1 and pow(2,N,3)==2
# Low digit zero lies in the support but is not the special 1063 digit.
assert 0 in set(range(943))-{1} and 0!=1063
rho=1<<67; low_mod=rho-2
assert low_mod%2==0 and ((rho-1)+low_mod+1)%rho==rho-2
# Low 67-bit consequence of 2n=R+1 (mod q^5) at C=beta.
assert ((rho-2)//2)%(1<<66)==(1<<66)-1
# Exact controls for the main Pell congruence and signed branches. They are
# not required to satisfy the other graph factors.
controls=0;examples=[]
for q in (2,4,8,16):
 for s in (1,2,3,4,6):
  a=q**3*s*(q+1);H=4*a+3;U=q**5*s;g=math.gcd(s,3)
  assert math.gcd(H,U)==g
  L=H//g; A=a+2; D=A*A-1
  x,y=1,0
  for m in range(0,28):
   assert x*x-D*y*y==1 and (x-a*y-pow(2,m,H))%H==0
   assert (x-a*y)*(x+a*y)%H==1%H
   assert y%2==m%2
   for sign in (1,-1):
    condition=(sign*x-a*y-q)%L==0
    if sign==1:expected=(pow(2,m,L)-q)%L==0
    else:expected=(-pow(pow(2,m,L),-1,L)-q)%L==0
    assert condition==expected
    if q%3==2 and s%3!=0 and condition:
     assert m%2==(1 if sign==1 else 0)
   x,y=A*x+D*y,x+A*y;controls+=1
# Nonempty small control: H=99, m=1 for positive, m=14 for negative.
q=2;s=1;a=q**3*s*(q+1);H=4*a+3
assert H==99 and (pow(2,1,H)-q)%H==0
assert (-pow(pow(2,14,H),-1,H)-q)%H==0
print(json.dumps({'fixed_N':N,'MC_mod_2_pow_67':'2^67-2',
 'first_index_n_mod_2_pow_66':'2^66-1',
 'signed_main_root_modulus':'(4*q^3*s*(q+1)+3)/gcd(s,3)',
 'signed_main_pell_controls':controls,'small_noncompact_control_H':H,
 'scope':'full zero, fixed compact tuple, F=0, J=1, C>0, w=1',
 'full_zero_excluded':False,'auxiliary_condition_decided':False,'lean_executed':False},indent=2,sort_keys=True))
