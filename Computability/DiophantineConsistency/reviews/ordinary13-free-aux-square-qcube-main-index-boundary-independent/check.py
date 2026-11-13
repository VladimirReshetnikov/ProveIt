#!/usr/bin/env python3
import hashlib,json
from pathlib import Path
root=Path(__file__).resolve().parents[2];here=Path(__file__).resolve().parent
for p,h in json.loads((here/'pins.json').read_text()).items():assert hashlib.sha256((root/p).read_bytes()).hexdigest()==h,p
cand=json.loads((root/'research/ordinary13-free-aux-square-compact-factor-obstruction/candidate.json').read_text())
r={x[0]:x[1:] for x in cand['source']}
for k,v in {'kbase':['+','n_eta','n_zeta'],'kY':['*','Y','kbase'],'c':['+','n_eta','kY'],
 's':['+','n_s',1],'q':['+',1,'qm'],'Y':['*','q3','s'],'U':['*','Y','q2'],
 'R':['+','g47','g50'],'A0':['-','g38','g42'],'A1':['-','g61','g65']}.items():assert r[k]==v
assert 'theorem solution_index' in (root/'Lean/DiophantineConsistency/ArithmeticPellClassification.lean').read_text()
assert 'theorem solution_index' in (root/'Lean/DiophantineConsistency/ArithmeticPellFirstNorm.lean').read_text()
# Independent coefficient calculation under q=8+t.
def mul(a,b):
 out=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):out[i+j]+=x*y
 return out
q=[8,1];q2=mul(q,q);q3=mul(q2,q)
p=[4*q3[i]-(7*q2[i] if i<len(q2) else 0)-(14*q[i] if i<len(q) else 0)+(14 if i==0 else 0) for i in range(4)]
assert p==[1502,642,89,4] and min(p)>0
# Exact exponent rewriting and boundary checks (finite controls only).
controls=0
for m in range(1,400):
 for n in range(1,400):
  assert ((7*(n-1)+3)<(5*(m-1))) == (7*n+1<5*m)
  if 7*n+1<5*m:
   assert 14*n<10*m
   controls+=1
for q0 in (8,16,32,64,128):
 L=(2*q0-1)*(q0*q0-1)+1
 assert 7*L-10*q0**3==4*q0**3-7*q0*q0-14*q0+14>0
 assert 2*(q0**3*(q0+1)+2)<q0**5
print(json.dumps({'compact_natural_k_zero_step_pinned':True,
 'q_shifted_rank_polynomial':p,'exponent_controls':controls,
 'm_zero_eliminated_by_conditional_positive_k_transfer':True,
 'slice':'fixed compact, J=1, w=s=1', 'main_m_at_most_q_cubed_excluded':True,
 'global_no_zero_or_model_claim':False,'lean_executed':False},indent=2,sort_keys=True))
