from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-pell-run-coordinate-wb-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
W=Path('research/ordinary13-pell-run-wb-composition-draft/PellRunWBComposition.lean.src').read_text()
C=Path('research/ordinary13-pell-coordinate-wb-draft/PellCoordinateWB.lean.src').read_text()
R=Path('Lean/DiophantineConsistency/ArithmeticPellRecurrence.lean').read_text()
G=Path('Lean/DiophantineConsistency/PRAWitnessPR.lean').read_text()
M=Path('Lean/DiophantineConsistency/PRAModelIOpenPairing.lean').read_text()
B=Path('research/ordinary13-pell-period-history-majorant-draft/PellHistoryMajorant.lean.src').read_text()
H=Path('research/ordinary13-pell-run-majorant-client-draft/PellRunMajorantClient.lean.src').read_text()
I=Path('research/ordinary13-pell-run-exponential-bound-draft/PellRunExponentialBound.lean.src').read_text()
for src in (W,C,G):
 for tok in ['[Nonempty M] [Structure language M] [Structure.Eq language M]', '[M↓[language] ⊧* PRA]',
 'local instance : Zero M', 'local instance : One M', 'local instance : Add M',
 'local instance : Mul M','local instance : LT M']:assert tok in src,tok
for tok in ['def blueprint : PR.Blueprint 1','noncomputable def construction : PR.Construction V blueprint',
 'def runDef : 𝚺₁.Semisentence 3 := blueprint.resultDef',
 '“out time b. ∃ state, !runDef state time b ∧ !pi₁Def out state”',
 '“out time b. ∃ state, !runDef state time b ∧ !pi₂Def out state”',
 'noncomputable def run (time b : V) : V := construction.result ![b] time']:assert tok in R,tok
for tok in ['(hz : WB M blueprint.zero.val) (hs : WB M blueprint.succ.val)',
 '(hH : PellValueMajorant) : WB M runDef.val','change WB M blueprint.resultDef.val',
 'PRAWitnessPR.wb_resultDef blueprint','hz hs pairValueBound hH',
 'PRAModelIOpenPairing.standardModelIOpen','(zero_wb (M := M)) (successor_wb (M := M)) pellValueMajorant']:assert tok in W,tok
for tok in ['theorem wb_resultDef {k : ℕ} (p : PR.Blueprint k)',
 '(hz : WB M p.zero.val) (hs : WB M p.succ.val) (H : BoundTerm (k + 2))',
 'i ≤ e 1 → (c V).result (fun j => e j.succ.succ) i ≤ H.vval e',
 'theorem wb_exs_bt\'','(hψ : Hierarchy 𝚺 1 ψ)','(A : BoundTerm n)',
 "ψ.Eval (x :> e) Empty.elim → ∃ x' ≤ A.vval e, ψ.Eval (x' :> e) Empty.elim",
 '(hWB : WB M ψ) : WB M (∃⁰ ψ)']:assert tok in G,tok
assert 'theorem standardModelIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻' in M
assert 'def PellValueMajorant : Prop' in B and 'fun j : Fin 1 => e j.succ.succ' in B
assert 'theorem pairValueBound_vval' in H and 'theorem pellValueMajorant : PellValueMajorant' in H
assert 'theorem run_le_exponential_horizon (i u a : V) (hi : i ≤ u)' in I
for tok in ['“state out time a. !runDef state time a ∧ !pi₁Def out state”',
 '“state out time a. !runDef state time a ∧ !pi₂Def out state”',
 'state = run (e 1) (e 2) ∧ e 0 = π₁ state',
 'state = run (e 1) (e 2) ∧ e 0 = π₂ state',
 '⟨state, ?_, h⟩','run_le_exponential_horizon (e 1) (e 1) (e 2) le_rfl',
 'change WB M (∃⁰ xStateBody)', 'change WB M (∃⁰ yStateBody)',
 "wb_exs_bt' xStateBody (by simp) pairValueBound",
 "wb_exs_bt' yStateBody (by simp) pairValueBound"]:assert tok in C,tok
# Natural controls of exact previous state and projection, with asymmetric slots.
for a in range(5):
 for time in range(7):
  x,y=1,0
  for _ in range(time):x,y=(a+2)*x+(a+1)*(a+3)*y,x+(a+2)*y
  state=y*y+x if x<y else x*x+x+y;bound=(2*2**(2*(a+2)*time)+1)**2
  assert state<=bound
  for out,projection in [(x,x),(y,y)]:
   e=[out,time,a];body=[state]+e
   assert body[1]==projection and body[2]==time and body[3]==a
assert (2*2**(2*(1+2)*3)+1)**2!=(2*2**(2*(3+2)*1)+1)**2
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'candidate_model_instances_and_hH_shape_checked':True,
 'coordinate_context_and_state_replacement_checked':True,
 'wb_exs_bt_hierarchy_and_body_WB_explicit':True,
 'lean_quote_simp_change_wb_auto_elaborated':False,
 'uniform_nested_witness_code_proved':False,'lean_executed':False},indent=2,sort_keys=True))
