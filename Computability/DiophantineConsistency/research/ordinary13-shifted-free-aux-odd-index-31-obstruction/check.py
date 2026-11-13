#!/usr/bin/env python3
"""Bounded modular certificate; never expand the fixed q or Pell iterates."""
import hashlib,json,math
from pathlib import Path
root=Path(__file__).resolve().parents[2];here=Path(__file__).resolve().parent
for p,h in json.loads((here/'pins.json').read_text()).items():assert hashlib.sha256((root/p).read_bytes()).hexdigest()==h,p
p='research/ordinary13-shifted85-free-aux-square-criterion/candidate.json'
r={x[0]:x[1:] for x in json.loads((root/p).read_text())['source']}
exp={'s':['+','n_s',1], 'q':['+',1,'qm'],'X':['*','q','n_w'],
 'Y':['*','q3','s'],'U':['*','Y','q2'],'kbase':['+','n_eta','n_zeta'],
 'k':['+','kbase',1],'c':['+','n_eta','kY'],'a':['+','E','Y'],
 'H':['+',3,'g15'],'Delta':['+','H','g17'], 'R':['+','g47','g50'],
 'r0':['-','kbase','R'],'Dstar':['+','g58','g59'],
 'rho':['-','f2',1],'Q':['*','Delta','rho'],'I':['*','c2','i'],
 'g72':['-','g71','Q'],'V':['-','g76','c'],'Fa':['-','n_y2','g82']}
for k,v in exp.items():assert r[k]==v,(k,r[k])
assert 'def betaNat : ℕ := 2^(67*8807)-1' in (root/'Lean/DiophantineConsistency/Compact44/CompactFixedBeta.lean').read_text()
N=67*8807
assert N==590069 and N>2 and pow(2,N,31)==16 and N>=3
# Binary multiplication in the Pell algebra (x+y sqrt(D)) modulo mod.
def power_pair(A,n,mod):
 D=(A*A-1)%mod
 def mul(u,v):return ((u[0]*v[0]+D*u[1]*v[1])%mod,(u[0]*v[1]+u[1]*v[0])%mod)
 ans=(1,0);cur=(A%mod,1)
 while n:
  if n&1:ans=mul(ans,cur)
  cur=mul(cur,cur);n//=2
 return ans
assert power_pair(2,8,31)==(0,14)
assert power_pair(2,32,31)==(1,0)
# Odd quotient Chebyshev sequence with I²=-3=28 mod 31.
a,b=1,16;seq=[]
for _ in range(16):
 seq.append(a);a,b=b,(17*b-a)%31
assert (a,b)==(1,16)
assert set(seq)=={1,3,8,15,16,23,28,30}
assert 4 not in seq and 27 not in seq
# Bounded universal-identity controls: y_{4A}(A) divisible by (2A)^2.
for A in range(2,201):
 assert power_pair(A,4*A,4*A*A)[1]==0
# Compact-exponent surrogate: q=8, s=31; only modular powers are computed.
q=8;s=31;Y=q**3*s;A=Y*(q+1)+2;c=2*A;h=4*A;H=4*Y*(q+1)+3;U=q**5*s
assert A%31==2 and A%8==2 and h%32==8
assert power_pair(A,h,c*c)[1]==0 and power_pair(A,h,31)[0]==0
assert math.gcd(H,U)==1 and H>4*q+1 and H>q-4>0
k=2*(q+1);eta=4;zeta=k-eta
assert zeta>=1 and eta+Y*k==c
print(json.dumps({'fixed_q_mod31':16,'actual_compact_A_mod31':2,'actual_compact_h_mod32':8,
 'Pell_pair_A2_index8_mod31':[0,14],'Pell_pair_A2_index32_mod31':[1,0],
 'odd_aux_quotients_mod31':sorted(set(seq)), 'excluded_target_residues':[4,27],
 'even_strong_index':'4*A', 'c_squared_divisibility_symbolic_argument':'README',
 'actual_signed_main_norm_for_m2':'impossible',
 'two_norm_child_zero_proved':False,'reverse_equivalence_refuted':False,
 'large_values_expanded':False,'lean_executed':False},indent=2,sort_keys=True))
