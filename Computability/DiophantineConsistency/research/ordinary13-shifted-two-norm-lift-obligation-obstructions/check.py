#!/usr/bin/env python3
"""Pinned graph and modular controls for three actual two-norm consequences."""
import hashlib,json,math
from pathlib import Path
root=Path(__file__).resolve().parents[2];here=Path(__file__).resolve().parent
for p,h in json.loads((here/'pins.json').read_text()).items():assert hashlib.sha256((root/p).read_bytes()).hexdigest()==h,p
g=json.loads((root/'research/ordinary9-shifted-free-aux-two-norm64/candidate.json').read_text());r={x[0]:x[1:] for x in g['source']}
expected={'s':['+','n_s',1],'qm':['*','n_J','beta'],'q':['+',1,'qm'],
 'X':['*','q','n_w'],'Y':['*','q3','s'],'U':['*','Y','q2'],
 'kbase':['+','n_eta','n_zeta'],'k':['+','kbase',1],'c':['+','n_eta','kY'],
 'a':['+','E','Y'],'H':['+',3,'g15'],'Delta':['+','H','g17'],
 'R':['+','g47','g50'],'r0':['-','kbase','R'],'shift':['-','g54','r0'],
 'Dstar':['+','g58','g59'],'A0':['-','g38','g42'],'A1':['-','g61','g65']}
for k,v in expected.items():assert r[k]==v,(k,r[k])
assert 'def betaNat : ℕ := 2^(67*8807)-1' in (root/'Lean/DiophantineConsistency/Compact44/CompactFixedBeta.lean').read_text()
N=67*8807;assert N==590069 and pow(2,N,5)==2 and N%2==1
assert 'theorem even_ordinate' in (root/'Lean/DiophantineConsistency/ArithmeticPellFirstNorm.lean').read_text()
# Exhaust the mod-five geometry for the two explicit subcases.
for w in range(5):
 for s in range(5):
  X=(2*w)%5;H=(4*pow(2,3,5)*s*(X+1)+3)%5
  if w==0 and s==1:assert X==0 and H==0
  if w==1 and s==2:assert X==2 and H==0
# Both signs of the main root force m=1 mod4 at H=0, X=2 mod5.
for m in range(4):
 p=pow(2,m,5);positive=(p==2);negative=((-pow(p,-1,5))%5==2)
 assert positive==(m==1) and negative==(m==1)
# Natural multiplier A is even, so the Pell ordinate parity is index parity.
for A in (2,4,6,8,10):
 x,y=1,0
 for m in range(20):
  assert y%2==m%2
  x,y=(A*x+(A*A-1)*y)%2,(x+A*y)%2
# Bounded controls for gcd(H,U)=gcd(s,3) at every power-of-two q.
for q in (8,32,128):
 for w in range(20):
  for s in range(1,15):
   H=4*q**3*s*(q*w+1)+3;U=q**5*s;g=math.gcd(s,3)
   assert math.gcd(H,U)==g
   if w%5==0 and s%5==1 and q%5==2:
    assert H%5==0 and (H//g)%5==0
print(json.dumps({'literal_graph_rows_checked':len(expected),'fixed_q_mod5':2,
 'main_norm_implies':'gcd(w,H/gcd(s,3))=1',
 'w_zero_mod5_s_one_mod5_excluded':True,
 'w_one_s_two_mod5_forces_main_index_mod4':1,
 'rank_minus_index_divisible_by_c_requires_m_odd':True,
 'full_graph_zero_constructed':False,'all_parent_lift_hypotheses_proved':False,
 'lean_executed':False},indent=2,sort_keys=True))
