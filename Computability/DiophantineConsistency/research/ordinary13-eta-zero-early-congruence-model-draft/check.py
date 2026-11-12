from pathlib import Path
from hashlib import sha256
from math import gcd
import json,random
p=Path('research/ordinary13-eta-zero-early-congruence-model-draft')
fs=[p/'EtaZeroEarlyCongruence.lean.src',p/'README.md',
Path('Lean/DiophantineConsistency/ArithmeticAdaptiveFactorThree2011.lean'),
Path('Lean/DiophantineConsistency/ArithmeticAdaptiveFirstDivisibility2011.lean'),
Path('Lean/DiophantineConsistency/Compact44/DirectMainNorm.lean'),
Path('research/ordinary13-residue-first-index-model-draft/ResidueFirstIndexModel.lean.src'),
Path('research/ordinary13-eta-zero-graph-adapter-audit/prototype.json')]
s=[f.read_text() for f in fs]
for x in ['theorem rank_congruence_of_balance','(hq : 0<q)','(hY : Y=q^3*s)',
 'cancel_factor_three q Y X','rank_congruence_of_main_norm','DirectMainNorm.direct_main_orientation',
 'early_index_of_actual_carrier','early_index_of_natural_norm','(hmain :','(hfirst :']:
 assert x in s[0],x
assert 'q = 3 * t + 2' not in s[0] and 'Bez ' not in s[0]
assert 'theorem cancel_factor_three' in s[2] and 'by_cases h3 : (3:V)∣q' in s[2]
g=json.loads(s[-1]);rows={r[0]:r for r in g['source']}
for row in [['r0','-','kbase','R'],['g54','*','U','n_gamma'],['shift','-','g54','r0'],['Dstar','+','g58','g59']]:assert rows[row[0]]==row
# For each case, the least positive t for q^5|H*t is a multiple of q^4.
# This finite check includes both 3|q and 3∤q; the model theorem is separate.
n=0
for q in range(1,70):
 for x in range(8):
  for st in range(1,5):
   Y=q**3*st;H=3+4*Y*(x+1);least=q**5//gcd(q**5,H)
   assert least%(q**4)==0
   n+=1
# The balance defect is exactly minus the rearranged congruence defect.
rng=random.Random(7068)
for _ in range(500):
 q=rng.randrange(1,8);X=rng.randrange(8);st=rng.randrange(1,5)
 Y=q**3*st;U=Y*q*q;H=3+4*(X*Y+Y)
 k,R,c,gamma,main=[rng.randrange(8) for _ in range(5)]
 car=U*main+H*k-U*(X+(X*Y+Y)*c)-H*(U*gamma+R+1)
 congr=H*(R+1)+q**5*(st*(X+(X*Y+Y)*c+H*gamma))-H*k-q**5*(st*main)
 assert car==-congr
print(json.dumps({'sha256':{str(f):sha256(f.read_bytes()).hexdigest() for f in fs},
 'finite_divisibility_controls':n,'balance_defect_controls':500,
 'three_divides_q_included':True,'no_q_mod_three_premise':True,'lean_executed':False,
 'proof_status':'unelaborated; actual graph factors and norm extraction remain open'},sort_keys=True,indent=2))
