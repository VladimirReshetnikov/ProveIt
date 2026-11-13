from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-pell-period-history-majorant-draft')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
checks={
 'Lean/DiophantineConsistency/PRAWitnessPR.lean':['theorem history_bound','theorem wb_resultDef {k : ℕ} (p : PR.Blueprint k)','(hz : WB M p.zero.val) (hs : WB M p.succ.val)','i ≤ e 1 → (c V).result (fun j => e j.succ.succ) i ≤ H.vval e','noncomputable def histT {k : ℕ}'],
 'Lean/DiophantineConsistency/ArithmeticConstructionBoundPell.lean':['theorem x_le (t b : V)','theorem y_le (t b : V)'],
 'Lean/DiophantineConsistency/ArithmeticPow.lean':['theorem power_iterate','theorem power_mono_base','theorem power_mono_exponent','theorem power_two'],
 'Lean/DiophantineConsistency/PRAWitnessRepeatVec.lean':['pair_polybound'],
 'Lean/DiophantineConsistency/PRAWitnessBoundTerms.lean':['inductive BoundTerm (n : ℕ)','| exp2 A B, e => Exp.exp (A.vval e * Exp.exp (B.vval e))'],
 'Lean/DiophantineConsistency/PRAWitnessArithmetic.lean':['theorem wb_pairDef','theorem wb_pi₁Def','theorem wb_pi₂Def'],
 'Lean/DiophantineConsistency/PRAWitnessCalculus.lean':['def WB {n : ℕ}','∃ B : (Fin n → M) → M, Mono M B'],
 'research/ordinary13-pell-period-history-majorant-draft/PellHistoryMajorant.lean.src':['def pairValueBound : BoundTerm 3','poly ‘2 * (#2 + 2) * #1’','PRAWitnessPR.histT (k := 1) pairValueBound','def PellValueMajorant : Prop','fun j : Fin 1 => e j.succ.succ']}
for p,toks in checks.items():
 s=Path(p).read_text()
 for x in toks:assert x in s,(p,x)
# Finite exact controls, never materializing the proposed history bound.
count=0
for a in range(7):
 A=a+2;delta=(a+1)*(a+3);base=2*A
 for u in range(9):
  F=2**(base*u);H=(2*F+1)**2;x,y=1,0
  for i in range(u+1):
   pair=y*y+x if x<y else x*x+x+y
   assert x<=F and y<=F and pair<=H
   x,y=A*x+delta*y,x+A*y
  count+=1
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),'source_interfaces_checked':len(checks),'paired_value_majorant_controls':count,'hH_statement_explicit_unproved':True,'raw_history_bound_not_full_period_bound':True,'lean_executed':False},sort_keys=True,indent=2))
