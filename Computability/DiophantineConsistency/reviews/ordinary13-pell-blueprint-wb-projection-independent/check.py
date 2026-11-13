from pathlib import Path
from hashlib import sha256
import json,re,sys,math
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-pell-blueprint-wb-projection-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
W=Path('research/ordinary13-pell-blueprint-wb-draft/PellBlueprintWB.lean.src').read_text()
P=Path('research/ordinary13-pell-blueprint-projection-bounds-draft/PellBlueprintProjectionBounds.lean.src').read_text()
R=Path('Lean/DiophantineConsistency/ArithmeticPellRecurrence.lean').read_text()
C=Path('Lean/DiophantineConsistency/PRAWitnessCalculus.lean').read_text()
A=Path('Lean/DiophantineConsistency/PRAWitnessArithmetic.lean').read_text()
B=Path('../../lib/FormalizedFormalLogic-Foundation/Foundation/FirstOrder/Arithmetic/IOpen/Basic.lean').read_text()
S=Path('../../lib/FormalizedFormalLogic-Foundation/Foundation/FirstOrder/Basic/Semantics/Semantics.lean').read_text()
for x in ['“out b. !pairDef out 1 0”','“out previous index b. ∃ x y,',
 '!pi₁Def x previous ∧ !pi₂Def y previous ∧',
 '!pairDef out ((b+2)*x+(b+1)*(b+3)*y) (x+(b+2)*y)”','zero := zeroDef','succ := succDef']:assert x in R
for x in ['“y x out previous index b. !pi₁Def x previous ∧ !pi₂Def y previous ∧',
 '!pairDef out ((b+2)*x+(b+1)*(b+3)*y) (x+(b+2)*y)”',
 '(∃⁰ succInner).Eval (x :> e) Empty.elim → x ≤ e 1',
 'succInner.Eval (y :> e) Empty.elim → y ≤ e 2',
 'change WB M (∃⁰ (∃⁰ succInner))','refine wb_exs_term ‘#1’',
 'refine wb_exs_term ‘#2’','(hx : FirstBound (M := M)) (hy : SecondBound (M := M))']:assert x in W,x
for x in ['e 1 = π₁ (e 3) ∧ e 0 = π₂ (e 3)',
 'e 2 = ⟪(e 5+2)*(e 1)+(e 5+1)*(e 5+3)*(e 0)',
 'simp [succInner, Semiformula.eval_substs]',
 '(succInner_eval (y :> e)).mp h','by simpa using hp.2.1',
 '(succInner_eval (y :> x :> e)).mp hy','by simpa using hp.1',
 'succ_wb_of_bounds (first_bound (M := M)) (second_bound (M := M))']:assert x in P,x
assert 'lemma eval_ex {φ : Semiformula L ξ (n + 1)}' in S
assert 'Eval b f (∃⁰ φ) ↔ ∃ x : M, Eval (x :> b) f φ' in S
assert 'theorem wb_exs_term {n : ℕ} {ψ : ArithmeticSemisentence (n + 1)}' in C
assert '(hb : ∀ (e : Fin n → M) (y : M), ψ.Eval (y :> e) Empty.elim → y ≤ t.val e Empty.elim)' in C
assert 'macro "wb_auto" : tactic => `(tactic| repeat\' wb_step)' in C
for n in ['wb_pairDef','wb_pi₁Def','wb_pi₂Def']:assert 'theorem '+n in A
for n in ['pi₁_le_self','pi₂_le_self','pair_defined','pi₁_defined','pi₂_defined']:assert n in B
assert 'pi₁Def.val.Evalb ![a,x] ↔ a = π₁ x := pi₁_defined.defined ![a,x]' in Path('Lean/DiophantineConsistency/PRAHistoryTruncation.lean').read_text()
# Independently check the de-Bruijn cons positions and the actual standard pairing.
controls=0
for previous in range(1000):
 k=math.isqrt(previous);z=previous-k*k;x,y=(z,k) if z<k else (k,z-k)
 assert (y*y+x if x<y else x*x+x+y)==previous
 assert x<=previous and y<=previous
 for b in range(3):
  left=(b+2)*x+(b+1)*(b+3)*y;right=x+(b+2)*y
  out=right*right+left if left<right else left*left+left+right
  outer=[out,previous,37,b];afterx=[x]+outer;full=[y]+afterx
  assert outer[1]==afterx[2]==full[3]==previous
  assert full[1]==x and full[0]==y and full[2]==out and full[5]==b
  assert full[2]==(right*right+left if left<right else left*left+left+right)
  controls+=1
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'quoted_source_and_two_binder_indices_inspected':True,'eval_ex_direction_inspected':True,
 'projection_graph_interfaces_inspected':True,'natural_transition_controls':controls,
 'quote_change_simp_wb_auto_elaborated':False,'upstream_imports_are_inert':True,
 'uniform_bound_or_ipra_proved':False,'lean_executed':False},indent=2,sort_keys=True))
