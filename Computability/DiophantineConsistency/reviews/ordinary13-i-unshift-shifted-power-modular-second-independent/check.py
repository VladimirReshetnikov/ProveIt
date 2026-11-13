from pathlib import Path
from hashlib import sha256
from math import isqrt
import json,sys,subprocess
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-i-unshift-shifted-power-modular-second-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
p0=Path('research/ordinary13-i-unshift-fixed-shifted-power-modular-obstructions')
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p0/'check.py')])==(p0/'receipt.json').read_bytes()
C=Path('Lean/DiophantineConsistency/Compact44');assert 'def betaNat : ℕ := 2^(67*8807)-1' in (C/'CompactFixedBeta.lean').read_text()
mask=(C/'CompactConcreteMask.lean').read_text();assert 'range 943 ∪ Ico 983 993 ∪ Ico 1003 1012 ∪ Ico 1013 1032' in mask and '{1063,1064,1095,2195,3296}) \\ {1}' in mask
assert 'if j=special then B-4 else if j∈S then B-2 else B-1' in (C/'CompactListMask.lean').read_text()
hs=(C/'CompactHighPopulation.lean').read_text()
for x in ('[4] ++ List.replicate 1012 0 ++ List.replicate 10 1','List.replicate 42 0 ++ List.replicate 9 1','List.replicate 1121 0 ++ [1] ++ List.replicate 1100 0 ++ [1]','List.replicate 1096 0 ++ [mu] ++ List.replicate 1101 0 ++ [mu]','List.replicate 3296 0 ++ List.replicate 13 padding ++ [lastPadding,0]','def mu : ℕ := 2^51-2','def padding : ℕ := 2^65-1','def lastPadding : ℕ := 2^19-1'):assert x in hs
support=(set(range(943))|set(range(983,993))|set(range(1003,1012))|set(range(1013,1032))|{1063,1064,1095,2195,3296})-{1}
low=[2**67-(4 if j==1063 else 2 if j in support else 1) for j in range(8807)]
high=[4]+[0]*1012+[1]*10+[0]*42+[1]*9+[0]*1121+[1]+[0]*1100+[1]+[0]*1096+[2**51-2]+[0]*1101+[2**51-2]+[0]*3296+[2**65-1]*13+[2**19-1,0]
assert len(low)==len(high)==8807
def digits(ds,base,m):
 r=0
 for x in reversed(ds):r=(r*base+x)%m
 return r
def residues(m):
 rho=pow(2,67,m);beta=(pow(rho,8807,m)-1)%m;lo=digits(low,rho,m);hi=digits(high,rho,m)
 return rho,beta,lo,hi,(beta+hi)%m
p=193707721;assert p%2==1 and all(p%i for i in range(3,isqrt(p)+1,2)) and pow(2,67,p)==1
assert residues(3)==(2,1,1,0,1) and residues(p)==(1,0,193706734,55802646,55802646)
R=(193706734+55802646)%p;disc=(8*R+12)%p
assert (R,disc,pow(disc,(p-1)//2,p))==(55801659,58997842,p-1)
assert [((2*L*(2*L+1)-1)%3) for L in range(3)]==[2,2,1]
for q in (1,2):assert ((q-1)*(1+q))%3==0
# Independently expand the exponent matching as a three-variable integer polynomial.
N=3;zero=(0,0,0)
def C(v):return {zero:v} if v else {}
def V(i):
 e=[0,0,0];e[i]=1;return {tuple(e):1}
def add(a,b,sgn=1):
 r=a.copy()
 for k,v in b.items():r[k]=r.get(k,0)+sgn*v
 return {k:v for k,v in r.items() if v}
def sub(a,b):return add(a,b,-1)
def mul(a,b):
 r={}
 for e,v in a.items():
  for f,w in b.items():
   k=tuple(x+y for x,y in zip(e,f));r[k]=r.get(k,0)+v*w
 return {k:v for k,v in r.items() if v}
L,n,d=[V(i) for i in range(3)];one=C(1);two=C(2);m=add(n,d)
E=sub(mul(sub(m,one),add(add(m,L),one)),add(add(one,L),mul(sub(n,one),add(add(m,mul(two,L)),two))))
condition=sub(mul(n,sub(add(L,one),d)),mul(d,add(add(d,L),one)))
assert E==sub({},condition)
for L0 in range(4,100):
 n0=L0*(L0-1);d0=L0-1;m0=n0+d0
 assert m0==L0*L0-1 and n0*(L0+1-d0)==d0*(d0+L0+1)
 assert 4*(m0-1)<2**(m0-L0)
# p-obstruction alone does not cover other J: choose t congruent to J mod p;
# q=(2^N)^t is power-of-two and (q-1)/beta is congruent to t mod p.
J=(-pow(R,-1,p))%p
assert J==113487015 and (J*R)%p==p-1 and (8*J*R+12)%p==4
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'author_receipt_reproduced':True,'separate_Horner_source_digits_mod3_and_p':True,
 'p_trial_division_to':isqrt(p),'legendre_residue':pow(disc,(p-1)//2,p),
 'general_power_matching_polynomial_identity':True,'L_offset_finite_controls':96,
 'other_J_power_two_residue_example':J,'rank_for_other_J_mod_p':(J*R)%p,
 'scope':'The second obstruction is J=1 only; no compact graph zero exclusion or model theorem.',
 'lean_executed':False},sort_keys=True,indent=2))
