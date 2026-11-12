from pathlib import Path
from hashlib import sha256
import json
p=Path('research/ordinary13-eta-zero-growth-model-draft')
fs=[p/'EtaZeroGrowth.lean.src',p/'README.md',
Path('Lean/DiophantineConsistency/ArithmeticPellPowerRecovery.lean'),
Path('research/ordinary13-eta-zero-direct-projection-model-draft/EtaZeroDirectProjection.lean.src'),
Path('research/ordinary13-eta-zero-graph-adapter-audit/prototype.json')]
s=[f.read_text() for f in fs]
for x in ['theorem growth','(hq : 16≤q)','(hw0 : 0<w0)','(hX : X=q*w0)',
 '(hY : Y=q^3*s)','(hindex : 2*n=R+1)','(hmainy :','(hfirst :',
 'power_bound X Y r k c eta zeta','theorem power','(hmainx :','(hcar :',
 'EtaZeroDirectProjectionDraft.power_of_direct_carrier']:
 assert x in s[0],x
assert 'theorem power_bound (X Y r k c eta zeta : V)' in s[2]
g=json.loads(s[4]);rows={r[0]:r for r in g['source']}
assert rows['X']==['X','*','q','n_w'] and rows['Y']==['Y','*','q3','s']
checks=0
for q in range(16,40):
 for w0 in range(1,7):
  for s0 in range(1,4):
   X=q*w0;Y=q**3*s0
   assert X>=16 and Y>=1
   assert 16*(2*(2*X*Y*Y+1)) < (2*(Y*(X+1))+3)**2
   checks+=1
for n in range(13,150):
 r=n-1;R=2*n-1
 assert r>=2 and R==2*r+1
print(json.dumps({'sha256':{str(f):sha256(f.read_bytes()).hexdigest() for f in fs},
 'prototype_input_and_gap_controls':checks,'index_controls':137,'lean_executed':False,
 'status':'unelaborated; graph extraction and all witness/port/provider premises remain open'},sort_keys=True,indent=2))
