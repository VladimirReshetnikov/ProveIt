#!/usr/bin/env python3
"""Graph wiring and bounded symbolic controls, not a main-norm witness."""
import hashlib,json,subprocess,sys
from pathlib import Path
root=Path(__file__).resolve().parents[2]; here=Path(__file__).resolve().parent
for p,h in json.loads((here/'pins.json').read_text()).items():assert hashlib.sha256((root/p).read_bytes()).hexdigest()==h,p
prev=root/'research/ordinary13-f-unshift-fixed-small-power-w-gcd'
r=subprocess.run([sys.executable,'-I','-S','-B',str(prev/'check.py')],cwd=root,check=True,text=True,capture_output=True)
assert r.stdout==(prev/'receipt.json').read_text()
g=json.loads((root/'research/ordinary9-shifted-free-aux-two-norm64/candidate.json').read_text())
r={x[0]:x[1:] for x in g['source']}
for k,v in {'F':['+','n_F',1],'alpha':['+','n_alpha',1],'qm':['*','n_J','beta'],
 'q':['+',1,'qm'],'X':['*','q','n_w'],'s':['+','n_s',1],'Y':['*','q3','s'],
 'U':['*','Y','q2'],'qF':['-','q','F'],'C':['-','qF','alpha'],
 'kbase':['+','n_eta','n_zeta'],'k':['+','kbase',1],'c':['+','n_eta','kY'],
 'Bt':['-','g27','F'],'Z':['-','g32','Bt'],'G':['+','alpha','g44'],
 'R':['+','g47','g50'],'r0':['-','kbase','R'],'Dstar':['+','g58','g59'],
 'A0':['-','g38','g42'],'A1':['-','g61','g65']}.items():assert r[k]==v,(k,r[k])
base=root/'Lean/DiophantineConsistency/Compact44'
assert 'def betaNat : ℕ := 2^(67*8807)-1' in (base/'CompactFixedBeta.lean').read_text()
assert 'range 943 ∪ Ico 983 993' in (base/'CompactConcreteMask.lean').read_text()
assert 'if j=special then B-4 else if j∈S then B-2 else B-1' in (base/'CompactListMask.lean').read_text()
N=67*8807; assert 67*5496< N-1 and N>=4
# Small positive algebra controls for the exact carrier and first-root identity.
checks=0
for beta in (7,15,31,63):
 t=(beta-1)//2;q=beta+1
 for Kp in range(t):
  for P in (1,2,5):
   w=t-Kp;K0=beta*P+Kp;X=q*w;C=q-3
   B=C*(X+K0)-1;h=C*(w+P)+t-1
   assert B==beta*h and h>0
   for k in (2,4,8):
    for ell,tau in ((0,1),(3,7),(10,12)):
     rr=tau-ell-k+(k*beta+1)*h
     if tau>ell:
      assert rr>=0 and beta*(ell+k+rr-k*B)-B==beta*tau
     checks+=1
# Noncompact toy q=8, exact rank and first Pell recurrence modulo 4M.
q=8;beta=q-1;Kp=2;P=2;t=(beta-1)//2;w=t-Kp;K0=beta*P+Kp
MC=2;MF=8;C=q-3;Y=q**3;U=q**5;M=q**7*w
B=C*(q*w+K0)-1;assert B>0 and B%beta==0
R=(beta*beta+2)*(q*q-1)+MC+q*MF
assert R%2==1 and R>0;n=(R+1)//2
# Pell unit powering modulo 4M, without constructing large ordinates.
mod=4*M;D=M*(M+1)
def mul(u,v):return ((u[0]*v[0]+D*u[1]*v[1])%mod,(u[0]*v[1]+u[1]*v[0])%mod)
ans=(1,0);cur=((2*M+1)%mod,2);e=n
while e:
 if e&1:ans=mul(ans,cur)
 cur=mul(cur,cur);e//=2
assert (ans[1]-2*n)%mod==0 and (ans[1]-(R+1))%U==0
print(json.dumps({'literal_nine_variable_rows_checked':21,'fixed_kernel_bound_reproduced':True,
 'carrier_root_bounded_controls':checks,'toy_first_index':n,
 'toy_k_minus_rank_divisible_by_U':True,'compact_rank_odd_by_mask_digit':True,
 'actual_compact_main_norm_solved':False,'full_zero_or_equivalence_proved':False,
 'fixed_beta_and_Kprime_reconstructed_in_predecessor_memory':True,
 'giant_Pell_values_expanded_or_large_numerals_written':False,'lean_executed':False},indent=2,sort_keys=True))
