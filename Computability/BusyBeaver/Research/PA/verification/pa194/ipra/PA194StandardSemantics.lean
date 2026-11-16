import PA194Bounded
import DiophantineConsistency.IPRAPA196Consistency

/-! Ordinary Tarskian interpretation in a classical structure. These are
standard-model identifications, not implications proved inside iPRA. -/
set_option autoImplicit false
noncomputable section
namespace PA194StandardSemantics
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.PRALanguage
open DiophantineConsistency.IPRANativeFormula
open DiophantineConsistency.IPRAPA196Consistency

variable {L : Language} {M : Type} [s : Structure L M] {ξ : Type}

def evalI (f : ξ → M) : {n : ℕ} → (Fin n → M) → Semiformulaᵢ L ξ n → Prop
  | _, _, .falsum => False
  | _, b, .rel r ts => s.rel r (fun i => (ts i).val b f)
  | _, b, .and p q => evalI f b p ∧ evalI f b q
  | _, b, .or p q => evalI f b p ∨ evalI f b q
  | _, b, .imp p q => evalI f b p → evalI f b q
  | _, b, .all p => ∀ x : M, evalI f (x :> b) p
  | _, b, .exs p => ∃ x : M, evalI f (x :> b) p

theorem eval_native (f : ξ → M) : ∀ {n : ℕ} (p : Semiformula L ξ n) (b : Fin n → M),
    evalI f b (native p) ↔ Semiformula.EvalAux s f b p
  | _, .verum, _ => by simp [evalI, native, Semiformula.EvalAux]
  | _, .falsum, _ => by simp [evalI, native, Semiformula.EvalAux]
  | _, .rel r ts, _ => by rfl
  | _, .nrel r ts, _ => by rfl
  | _, .and p q, b => by simp [evalI, native, Semiformula.EvalAux, eval_native f p b, eval_native f q b]
  | _, .or p q, b => by simp [evalI, native, Semiformula.EvalAux, eval_native f p b, eval_native f q b]
  | _, .all p, b => by simp [evalI, native, Semiformula.EvalAux, eval_native f p]
  | _, .exs p, b => by simp [evalI, native, Semiformula.EvalAux, eval_native f p]

local instance : Structure language ℕ := natStructure

theorem consistency_standard :
    evalI (M := ℕ) Empty.elim ![] nativePAConsistency ↔ Entailment.Consistent (𝗣𝗔 : ArithmeticTheory) := by
  change ¬evalI Empty.elim ![] (native mappedPARefutation) ↔ _
  rw [eval_native]
  change ¬Semiformula.Eval (s := natStructure) ![] Empty.elim mappedPARefutation ↔ _
  unfold mappedPARefutation
  rw [DiophantineConsistency.PRALanguage.nat_formula_map]
  have hs := paConsistency_standard
  rw [paConsistency_eq] at hs
  rw [LogicalConnective.HomClass.map_neg] at hs
  exact hs

theorem halting_standard :
    evalI (M := ℕ) Empty.elim ![] PA194Bounded.haltSentence ↔
      M6.Zip.Halts PA194.Literal.machine PA194Bounded.blankZip := by
  change (∃ n : ℕ, Semiterm.val ![n] Empty.elim PA194Bounded.boundedTerm = 1) ↔ _
  exact PA194Bounded.term_halts_iff_literal

#print axioms consistency_standard
#print axioms halting_standard
end PA194StandardSemantics
