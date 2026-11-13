from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-pell-run-exponential-bound-draft')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
checks={
 'Lean/DiophantineConsistency/ArithmeticConstructionBoundPell.lean':['theorem x_le (t b : V)','theorem y_le (t b : V)','theorem one_le_two_mul_add_two (b : V)'],
 'Lean/DiophantineConsistency/ArithmeticPow.lean':['theorem power_iterate (x m n : V)','theorem power_mono_base (x y n : V)','theorem power_mono_exponent (x m n : V)','theorem power_two (n : V)'],
 'Lean/DiophantineConsistency/ArithmeticPellRecurrence.lean':['noncomputable def xcoord','noncomputable def ycoord'],
 'Lean/DiophantineConsistency/PRAWitnessRepeatVec.lean':['pair_polybound'],
 '../../lib/FormalizedFormalLogic-Foundation/Foundation/FirstOrder/Arithmetic/IOpen/Basic.lean':['lemma pair_unpair','lemma pair_polybound'],
 '../../lib/FormalizedFormalLogic-Foundation/Foundation/FirstOrder/Arithmetic/Exponential/Exp.lean':['lemma lt_exp (a : V)'],
 'research/ordinary13-pell-run-exponential-bound-draft/PellRunExponentialBound.lean.src':['theorem run_le_of_coord_bound','pair_polybound (xcoord i a) (ycoord i a)','theorem power_le_binary_exponential','theorem run_le_exponential_horizon','i ≤ u'],
 'research/ordinary13-pell-period-history-majorant-draft/PellHistoryMajorant.lean.src':['def pairValueBound : BoundTerm 3','poly ‘2 * (#2 + 2) * #1’','def PellValueMajorant : Prop']}
for p,toks in checks.items():
 s=Path(p).read_text()
 for t in toks:assert t in s,(p,t)
count=0
for a in range(11):
 A=a+2;Delta=(a+1)*(a+3);base=2*A
 for u in range(10):
  F=2**(base*u);bound=(2*F+1)**2;x,y=1,0
  assert base**u<=F
  for i in range(u+1):
   pair=y*y+x if x<y else x*x+x+y
   assert x<=base**i<=base**u<=F and y<=base**i and pair<=bound
   x,y=A*x+Delta*y,x+A*y
   count+=1
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),'source_interfaces_checked':len(checks),'paired_state_controls':count,'run_horizon_theorem_elaborated':False,'boundterm_semantic_identification_proved':False,'lean_executed':False},sort_keys=True,indent=2))
