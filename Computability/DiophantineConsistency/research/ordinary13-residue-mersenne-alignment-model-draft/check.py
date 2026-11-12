from pathlib import Path
from hashlib import sha256
import json
p=Path('research/ordinary13-residue-mersenne-alignment-model-draft')
fs=[p/'ResidueMersenneAlignment.lean.src',p/'README.md',
Path('Lean/DiophantineConsistency/ArithmeticAdaptiveMersenne2011.lean'),
Path('Lean/DiophantineConsistency/ArithmeticRadixAlignment.lean'),
Path('research/ordinary13-residue-signfree-power-model-draft/ResidueSignFreePower.lean.src')]
s=fs[0].read_text()
for v in ['theorem divides_power','theorem alignment','(hd : 4≤d)','(hJ : 0<J)','(hq :','(hpower :','(hthree :','cancel_three','factor_alignment']:
 assert v in s,v
cases=0
for d in range(4,9):
 for j in range(1,16):
  q=(2**d-1)*j+1
  for r in range(20):
   if (3*2**r)%q==0:
    assert (2**r)%q==0
    cases+=1
print(json.dumps({'sha256':{str(f):sha256(f.read_bytes()).hexdigest() for f in fs},
 'finite_positive_test_cases':cases,'lean_executed':False,
 'proof_status':'unelaborated; graph and port interfaces remain open'},sort_keys=True,indent=2))
