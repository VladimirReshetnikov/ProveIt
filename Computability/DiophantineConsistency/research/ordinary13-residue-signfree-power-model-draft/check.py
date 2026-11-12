from pathlib import Path
from hashlib import sha256
import json
p=Path('research/ordinary13-residue-signfree-power-model-draft')
files=[p/'ResidueSignFreePower.lean.src',p/'README.md',
 Path('Lean/DiophantineConsistency/ArithmeticPellPowerRecovery.lean'),
 Path('Lean/DiophantineConsistency/Compact44/FreeJPowerFinish.lean'),
 Path('research/ordinary13-residue-three-projection-model-draft/ResidueThreeProjection.lean.src'),
 Path('research/ordinary13-residue-three-projection-graph-draft/ResidueThreeProjectionGraph.lean.src'),
 Path('research/ordinary13-residue-aux-bounds-adapter-draft/ResidueExactIndexFromGraph.lean.src')]
s=files[0].read_text()
for x in ['sixteen_of_three_projection','46≤q','q∣3*X','growth_of_coordinates','hfirst :','power_bound','power_of_oriented_balance','projection_quotient','hbalance :','mod_cancel']:
 assert x in s,x
for q in range(46,100):
 for X in range(1,80):
  if 3*X%q==0: assert X>=16
# Compare the difference in the natural balance against the scaled signed
# q-balance for unrestricted small natural valuations, including failure cases.
count=0
for q in range(1,6):
 for X in range(1,6):
  for s0 in range(1,4):
   Y=q**3*s0; a=Y*(X+1); H=3+4*a; d=4*q*q*s0*(X+1)
   for main in range(5):
    for gamma in range(3):
     for W in range(3):
      c=2
      lhs=3*(X+a*c)+H*(main+H*W+3*gamma)
      rhs=3*main+H*(3*W+X+a*c+H*gamma+d*X)
      defect=q*(main+H*W)-q*(X+a*c+H*gamma)-H*X
      assert lhs-rhs==d*defect
      count+=1
print(json.dumps({'sha256':{str(f):sha256(f.read_bytes()).hexdigest() for f in files},
 'lower_bound_test_q':'46..99','balance_identity_assignments':count,
 'lean_executed':False,'proof_status':'unelaborated; hypotheses and provider boundaries remain open'},indent=2,sort_keys=True))
