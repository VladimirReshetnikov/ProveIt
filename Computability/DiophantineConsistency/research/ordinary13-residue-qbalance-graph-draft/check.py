from pathlib import Path
from hashlib import sha256
import json
p=Path('research/ordinary13-residue-qbalance-graph-draft')
fs=[p/'ResidueQBalance.lean.src',p/'ResidueQBalanceGraph.lean.src',p/'README.md',
Path('research/ordinary13-residue-three-projection-graph-draft/ResidueThreeProjectionGraph.lean.src'),
Path('research/ordinary13-residue-aux-bounds-adapter-draft/ResidueExactIndexFromGraph.lean.src'),
Path('research/ordinary13-residue-signfree-power-model-draft/ResidueSignFreePower.lean.src'),
Path('research/ordinary13-residue90-norm-model-draft/Residue90GraphNorms.lean.src'),
Path('Lean/DiophantineConsistency/Compact44/FreeJPowerFinish.lean')]
s=[f.read_text() for f in fs]
for x in ['let W:=4*X*q*s*w','(hq : 0<q)','(hYpos : 0<Y)','(hindex :','(hroot :','mul_left_cancel₀','4*(X*Y*Y)*w=U*W']:
 assert x in s[0],x
for x in ['actual_q_balance','actual_main_balance','exact_indices_of_graph','(v 7+1)*w','actual_power_of_pell_coordinates','(hmainx :','(hmainy :','(hfirst :','(hq46 :','have ha : a p v=Y p v*(v 6+1)']:
 assert x in s[1],x
count=0
for q in range(1,7):
 for X in range(1,5):
  for st in range(1,4):
   for w in range(4):
    for main in range(4):
     Y=q**3*st;U=Y*q*q;W=4*X*q*st*w; a=X*Y+Y; H=3+4*a
     R=7;gamma=2;c=3;k=R+1+4*X*Y*Y*w
     assert 4*X*Y*Y*w==U*W
     root=U*main+H*k-U*(X+a*c)-H*(U*gamma+X*Y*q+R+1)
     projected=q*(main+H*W)-q*(X+a*c+H*gamma)-H*X
     assert root==q*Y*projected
     count+=1
print(json.dumps({'sha256':{str(f):sha256(f.read_bytes()).hexdigest() for f in fs},
 'oriented_defect_identity_cases':count,'lean_executed':False,
 'proof_status':'unelaborated; recurrence witnesses, compact model ports and provider boundaries remain open'},sort_keys=True,indent=2))
