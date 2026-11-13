from pathlib import Path
from hashlib import sha256
import json,sys,re
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-pell-period-history-majorant-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
P=Path('research/ordinary13-pell-period-history-majorant-draft/PellHistoryMajorant.lean.src').read_text()
rec=Path('Lean/DiophantineConsistency/ArithmeticPellRecurrence.lean').read_text()
raw=Path('Lean/DiophantineConsistency/PRAWitnessPR.lean').read_text()
terms=Path('Lean/DiophantineConsistency/PRAWitnessBoundTerms.lean').read_text()
bounds=Path('Lean/DiophantineConsistency/ArithmeticConstructionBoundPell.lean').read_text()
calc=Path('Lean/DiophantineConsistency/PRAWitnessCalculus.lean').read_text()
pair=Path('Lean/DiophantineConsistency/PRAWitnessVectors.lean').read_text()
for x in ['def blueprint : PR.Blueprint 1','noncomputable def construction : PR.Construction V blueprint',
 'noncomputable def run (time b : V) : V := construction.result ![b] time',
 'def runDef : 𝚺₁.Semisentence 3 := blueprint.resultDef',
 'noncomputable def xcoord (time b : V) : V := π₁ (run time b)',
 'noncomputable def ycoord (time b : V) : V := π₂ (run time b)']:assert x in rec,x
assert 'theorem x_le (t b : V) : xcoord t b ≤ power (2 * (b + 2)) t' in bounds
assert 'theorem y_le (t b : V) : ycoord t b ≤ power (2 * (b + 2)) t' in bounds
assert '⟪b, c⟫ ≤ (b + c + 1) * (b + c + 1)' in pair
for x in ['def pairValueBound : BoundTerm 3', 'exp2 (poly ‘2 * (#2 + 2) * #1’) (poly ‘0’)',
 'add (add F F) (poly ‘1’)', 'mul S S', 'def rawHistoryBound : BoundTerm 3',
 'PRAWitnessPR.histT (k := 1) pairValueBound', 'def PellValueMajorant : Prop',
 '(e : Fin 3 → V) (i : V)', 'i ≤ e 1 →', 'fun j : Fin 1 => e j.succ.succ']:
 assert x in P,x
assert '| exp2 A B, e => Exp.exp (A.vval e * Exp.exp (B.vval e))' in terms
for x in ['{u z s F : V} (hs : c.CSeq v s) (huz : ⟪u, z⟫ ∈ s)',
 '(hF : ∀ i ≤ u, c.result v i ≤ F)',
 "s' < Exp.exp ((u + 1 + (F + 1) + 1) * (u + 1 + (F + 1) + 1))",
 '(hz : WB M p.zero.val) (hs : WB M p.succ.val)',
 'i ≤ e 1 → (c V).result (fun j => e j.succ.succ) i ≤ H.vval e',
 'WB M p.resultDef.val', 'noncomputable def histT {k : ℕ}']:
 assert x in raw,x
assert '∃ B : (Fin n → M) → M, Mono M B' in calc
assert '∀ e, φ.Eval e Empty.elim → (bnd φ).Eval (Fin.snoc e (B e)) Empty.elim' in calc
# Concrete independent checks of the inequality chain, without assuming a
# particular encoding of pairs beyond the source theorem pair_polybound.
tests=0
for a in range(7):
 B=2*(a+2);A=a+2;delta=(a+1)*(a+3)
 for u in range(9):
  F=2**(B*u);H=(2*F+1)**2;x,y=1,0
  for i in range(u+1):
   assert max(x,y)<=B**i<=2**(B*i)<=F
   assert (x+y+1)**2<=H
   x,y=A*x+delta*y,x+A*y
   tests+=1
# Outer horizon arithmetic for small cases; history exponent is not built.
for a in range(3):
 B=2*(a+2);A=a+2;delta=(a+1)*(a+3);x,c=1,0
 for m in range(3):
  if m:x,c=A*x+delta*c,x+A*c
  C=2**(B*m);U=2*m*C;h=2*m*c
  assert c<=C and m<=U and h<=U
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'three_argument_context_and_boundterm_interpretation_checked':True,
 'history_and_model_WB_interfaces_checked':True,'bounded_pair_inequality_controls':tests,
 'outer_horizon_controls':9,'raw_history_not_full_nested_witness_bound':True,
 'proposed_majorant_theorem_elaborated':False,'lean_executed':False},indent=2,sort_keys=True))
