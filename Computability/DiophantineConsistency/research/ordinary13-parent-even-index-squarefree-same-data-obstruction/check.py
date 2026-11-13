#!/usr/bin/env python3
"""Pinned factor/source checks and finite controls for the squarefree corollary."""
import hashlib,json,math,subprocess,sys
from pathlib import Path
root=Path(__file__).resolve().parents[2];here=Path(__file__).resolve().parent
for p,h in json.loads((here/'pins.json').read_text()).items():assert hashlib.sha256((root/p).read_bytes()).hexdigest()==h,p
prev=root/'research/ordinary13-parent-even-main-strong-pell-obstruction'
r=subprocess.run([sys.executable,'-I','-S','-B',str(prev/'check.py')],cwd=root,check=True,text=True,capture_output=True)
assert r.stdout==(prev/'receipt.json').read_text()
g=json.loads((root/'research/ordinary13-eta-zero-graph-adapter-audit/prototype.json').read_text());rows={x[0]:x[1:] for x in g['source']}
for k,v in {'Delta':['+','H','g17'],'rho':['-','f2',1], 'Q':['*','Delta','rho'],
 'I':['*','c2','i'],'g72':['-','g71','Q'],'Fs':['+',1,'g72'],
 'Fa':['-','y2','g82'],'P01':['*','F0','F1'],'P012':['*','P01','Fa'],
 'P0123':['*','P012','Fs'],'out':['-','P0123',1]}.items():assert rows[k]==v,(k,rows[k])
assert 'theorem solution_index' in (root/'Lean/DiophantineConsistency/ArithmeticPellClassification.lean').read_text()
# Exhaust the strong unit-factor mod-four exclusions with no sign assumptions.
for a in range(4):
 for f in range(4):
  for I in range(4):assert (1+I*I-(a*a+4*a+3)*(f*f-1))%4!=3
# Pell ordinate congruence/gcd identity, bounded ordinary integer controls.
controls=0
for A in range(2,35):
 D=A*A-1;x,y=1,0
 for m in range(1,41):
  x,y=A*x+D*y,x+A*y
  assert (y-m*pow(A,m-1,D))%D==0
  assert math.gcd(y,D)==math.gcd(m,D)
  controls+=1
# Exhaust the elementary squarefree divisibility implication at small D.
def squarefree(n):return all(n%(p*p)!=0 for p in range(2,math.isqrt(n)+1))
for D in range(1,100):
 if squarefree(D):
  for I in range(150):
   if I*I%D==0:assert I%D==0
# Independent exact illustrative A=2,m=2 strong witness (not a graph zero).
A=2;D=3;m=2;c=4;x,y=1,0
for _ in range(8):x,y=A*x+D*y,x+A*y
assert squarefree(D) and math.gcd(m,D)==math.gcd(c,D)==1
I=D*y;assert I%(c*c)==0 and I*I==D*(x*x-1)
print(json.dumps({'strong_mod4_cases':64,'pell_gcd_identity_controls':controls,
 'squarefree_divisibility_checked':True,'toy_A_m_D_c':[A,m,D,c],
 'conditional_same_data_parent_completion_excluded':True,
 'compact_two_norm_witness_exists':False,'existential_inequivalence_proved':False,
 'lean_executed':False},indent=2,sort_keys=True))
