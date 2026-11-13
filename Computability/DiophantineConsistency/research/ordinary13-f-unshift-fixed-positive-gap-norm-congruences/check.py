#!/usr/bin/env python3
"""Bounded exact checks accompanying the F=0 norm-congruence argument."""
import hashlib,json,math
from pathlib import Path
root=Path(__file__).resolve().parents[2]; here=Path(__file__).resolve().parent
for name,digest in json.loads((here/'pins.json').read_text()).items():
 assert hashlib.sha256((root/name).read_bytes()).hexdigest()==digest,name
path='research/ordinary13-eta85-shift-boundary-probes/F-probe.json'
g=json.loads((root/path).read_text()); rows={x[0]:x[1:] for x in g['source']}
w={'alpha':['+','n_alpha',1], 'qm':['*','n_J','beta'], 'q':['+',1,'qm'],
 'X':['*','q','n_w'], 'Y':['*','q3','s'], 'U':['*','Y','q2'],
 'qF':['-','q','n_F'],'C':['-','qF','alpha'], 'kbase':['+','n_eta','n_zeta'],
 'k':['+','kbase',1], 'ell':['*','E','kY'], 'Bt':['-','g27','n_F'],
 'Z':['-','g32','Bt'], 'g44':['*','qF','qm'], 'G':['+','alpha','g44'],
 'g46':['-','q2',1], 'g47':['*','G','g46'], 'g48':['*','MF','q'],
 'g49':['+','MC','g48'], 'g50':['*','n_J','g49'], 'R':['+','g47','g50'],
 'r0':['-','kbase','R'], 'shift':['-','g54','r0'], 'Dstar':['+','g58','g59'],
 'A0':['-','g38','g42'],'A1':['-','g61','g65']}
for key,value in w.items(): assert rows[key]==value,(key,rows[key])
source=(root/'Lean/DiophantineConsistency/ArithmeticPellFirstNorm.lean').read_text()
for s in ('theorem solution_index','theorem even_ordinate','theorem descent',
          '∃ y : V, k=2*y','2*ycoord time (2*q+1)=k'):
 assert s in source,s
fixed=(root/'Lean/DiophantineConsistency/Compact44/CompactFixedBeta.lean').read_text()
assert 'def betaNat : ℕ := 2^(67*8807)-1' in fixed
mask=(root/'Lean/DiophantineConsistency/Compact44/CompactConcreteMask.lean').read_text()
digit=(root/'Lean/DiophantineConsistency/Compact44/CompactListMask.lean').read_text()
assert 'range 943 ∪ Ico 983 993' in mask
assert 'if j=special then B-4 else if j∈S then B-2 else B-1' in digit
assert 0 in set(range(943))-{1} and 0!=1063
# Small exact recurrence controls. The proof is the universal descent in README.
cases=0
for M in range(1,30):
 x,k=1,0
 for n in range(9):
  assert x*x==1+M*(M+1)*k*k
  assert k%2==0 and (k-2*n)%(4*M)==0
  x,k=(2*M+1)*x+2*M*(M+1)*k, 2*x+(2*M+1)*k
  cases+=1
# Fixed-port mod-q form and q^5 cancellation: generic even powers q, not full graph samples.
for q in (8,16,32,64):
 for C in range(1,q):
  for MC in range(0,q-1,2):
   MF=q-1+4
   R=(q*q-C)*(q*q-1)+MC+q*MF
   assert (R-(C+MC))%q==0
   if (R+1)%2==0: assert C%2==1
 for s in (1,2,3,7):
  Y=q**3*s; U=Y*q*q; H=4*Y+3
  assert math.gcd(H,q**5)==1 and U%(q**5)==0
print(json.dumps({'graph_rows_checked':len(w), 'fixed_MC_even_from_digit_zero':True,
 'first_pell_recurrence_controls':cases, 'first_index_congruence_mod_4M':True,
 'main_rank_congruence_mod_q5':True, 'C_odd_necessary':True,
 'fixed_port_zero_proved':False,'fixed_port_zero_excluded':False,
 'graph_factor_extraction_assumed':True,'all_model_or_Lean_proof':False},indent=2,sort_keys=True))
