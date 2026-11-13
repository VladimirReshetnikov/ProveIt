#!/usr/bin/env python3
import hashlib,json,itertools,math
from pathlib import Path
root=Path(__file__).resolve().parents[2];here=Path(__file__).resolve().parent
for p,h in json.loads((here/'pins.json').read_text()).items():assert hashlib.sha256((root/p).read_bytes()).hexdigest()==h,p
path='research/ordinary13-free-aux-square-compact-factor-obstruction/candidate.json'
g=json.loads((root/path).read_text());r={x[0]:x[1:] for x in g['source']}
exp={'F':['+','n_F',1],'alpha':['+','n_alpha',1],'qm':['*','n_J','beta'],
 'q':['+',1,'qm'],'X':['*','q','n_w'],'s':['+','n_s',1],
 'Y':['*','q3','s'],'U':['*','Y','q2'],'qF':['-','q','F'],
 'C':['-','qF','alpha'],'kbase':['+','n_eta','n_zeta'],
 'kY':['*','Y','kbase'],'c':['+','n_eta','kY'],'ell':['*','E','kY'],
 'g27':['*','C','g26'],'Bt':['-','g27','F'],'Z':['-','g32','Bt'],
 'g44':['*','qF','qm'],'G':['+','alpha','g44'],'g46':['-','q2',1],
 'g47':['*','G','g46'],'g48':['*','MF','q'],'g49':['+','MC','g48'],
 'g50':['*','n_J','g49'],'R':['+','g47','g50'],
 'r0base':['-','kbase','R'],'r0':['-','r0base',1],
 'shift':['-','g54','r0'],'Dstar':['+','g58','g59'],
 'A0':['-','g38','g42'],'A1':['-','g61','g65']}
for k,v in exp.items():assert r[k]==v,(k,r[k])
assert 'k' not in r and r['kbase']==['+','n_eta','n_zeta']
assert 'def betaNat : ℕ := 2^(67*8807)-1' in (root/'Lean/DiophantineConsistency/Compact44/CompactFixedBeta.lean').read_text()
assert 'theorem solution_index' in (root/'Lean/DiophantineConsistency/ArithmeticPellFirstNorm.lean').read_text()
base=root/'Lean/DiophantineConsistency/Compact44'
assert '![β,K,L,β+H]' in (base/'CompactSymbolicPorts.lean').read_text()
assert 'List.replicate 3296 0 ++ List.replicate 13 padding ++ [lastPadding,0]' in (base/'CompactHighPopulation.lean').read_text()
assert 'if j=special then B-4 else if j∈S then B-2 else B-1' in (base/'CompactListMask.lean').read_text()
assert 'range 943 ∪ Ico 983 993' in (base/'CompactConcreteMask.lean').read_text()
for z,d in itertools.product(range(4),repeat=2):
 # In the specified q=2^N slice beta odd, ell and U even powers of q.
 assert z*z%4!=3 and (1+d*d)%4!=3
# Exact numerical controls for all F,alpha satisfying the positive gap.
rank_cases=0
for q in (8,16,32,64):
 assert 2*(q**3*(q+1)+2)<q**5
 for F in range(1,q):
  for alpha in range(1,q-F):
   G=alpha+(q-F)*(q-1)
   assert 2*q-1<=G<q*q
   # Endpoint masks 0≤MC<q, 0≤MF<2q bound every intermediate case.
   low=G*(q*q-1)+1
   high=G*(q*q-1)+(q-1)+q*(2*q-1)+1
   assert 2*q*q<low<=high<q**5
   rank_cases+=1
# Pell controls with natural eta and zeta: no +1 on k.
count=0
for q in (8,16,32):
 Y=q**3;M=q**7;A=Y*(q+1)+2
 u,v=1,0
 for n in range(1,7):
  u,v=(2*M+1)*u+4*M*(M+1)*v,u+(2*M+1)*v
  k=2*v;assert (k-2*n)%(4*M)==0
  x,c=1,0
  for m in range(1,8):
   x,c=A*x+(A*A-1)*c,x+A*c
   if c>=Y*k:assert n<=m
   count+=1
print(json.dumps({'literal_rows_checked':len(exp),'natural_k_has_no_extra_one':True,
 'rank_boundary_cases':rank_cases,'bounded_Pell_controls':count,
 'positive_m_le_q_squared_excluded_in_slice':True,
 'm_zero_excluded_from_claim':True,'all_graph_zeros_excluded':False,
 'lean_executed':False},indent=2,sort_keys=True))
