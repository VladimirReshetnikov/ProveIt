import DiophantineConsistency.PRAWitnessPR
import Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1

/-! Bounds for the quantifier-closure conjunct appearing in both polarities of
Foundation's unrestricted-induction recognizer. This does not bound the other
recognizer conjuncts. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace PA196InductionClosureWitness
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.PRAFiniteFunctionCodes DiophantineConsistency.PRALanguage
open DiophantineConsistency.PRATheory DiophantineConsistency.PRAWitnessCalculus
open DiophantineConsistency.PRAWitnessPR DiophantineConsistency.PRAWitnessBoundTerms
open DiophantineConsistency.PRAWitnessBoundTerms.BoundTerm
open DiophantineConsistency.PRAWitnessTransfer
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

/-- The positive closure graph, with free indices ordered as body, count, result. -/
noncomputable def closurePositive : ArithmeticSemisentence 3 :=
  Rewriting.subst qqAllsDef.val ![#2,#0,#1]
/-- Counterexample to the negative-polarity universal closure graph. -/
noncomputable def closureCounterexample : ArithmeticSemisentence 3 :=
  ∃⁰ (Rewriting.subst qqAllsDef.val ![#0,#1,#2] ⋏
    Semiformula.nrel Language.ORing.Rel.eq ![#0,#3])
/-- This universal clause is present in `chUniv.pi`. -/
noncomputable def closureCondition : ArithmeticSemisentence 3 :=
  “b m p. ∀ y, !qqAllsDef y b m → y = p”

theorem counterexample_eq_neg : closureCounterexample = ∼closureCondition := by
  simp [closureCounterexample, closureCondition, Semiformula.neg_all,
    Semiformula.imp_eq, DeMorgan.or, Rewriting.subst,
    Semiformula.Operator.operator, Semiformula.Operator.Eq.eq,
    Rewriting.emb]
  constructor
  · rfl
  · funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ j =>
      cases j using Fin.cases with
      | zero => rfl
      | succ j => exact Fin.elim0 j

/-- Extract the first unbounded graph conjunct under the two bounded
quantifiers in the actual positive recognizer. -/
noncomputable def actualPositiveClosure : ArithmeticSemisentence 3 :=
  match chUniv.sigma.val with
  | .exs (.and _ (.exs (.and _ (.and head _)))) => head
  | _ => ⊥

/-- Extract its universal analogue in the actual negative recognizer. -/
noncomputable def actualNegativeClosure : ArithmeticSemisentence 3 :=
  match chUniv.pi.val with
  | .exs (.and _ (.exs (.and _ (.and head _)))) => head
  | _ => ⊥

theorem positiveClosure_exact : actualPositiveClosure = closurePositive := by rfl
theorem negativeClosure_exact : actualNegativeClosure = closureCondition := by rfl

theorem wb_closurePositive : WB M closurePositive := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := DiophantineConsistency.PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  unfold closurePositive
  exact wb_rew _ (wb_qqAllsDef (M := M))

theorem wb_closureCounterexample : WB M closureCounterexample := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := DiophantineConsistency.PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_qqAllsDef (M := M)
  unfold closureCounterexample
  exact wb_exs_bt _ (by simp) (tauT (poly ‘#0’) (poly ‘2 * #1’))
    (fun V _ _ e x h => by
      have h' := h; simp at h'
      rw [h'.1]; simpa [vval_tauT, vval] using qqAlls_le (e 0) (e 1)) (by wb_auto)

theorem wb_neg_closureCondition : WB M (∼closureCondition) := by
  rw [←counterexample_eq_neg]
  exact wb_closureCounterexample

theorem wb_actualPositiveClosure : WB M actualPositiveClosure := by
  rw [positiveClosure_exact]
  exact wb_closurePositive

theorem wb_neg_actualNegativeClosure : WB M (∼actualNegativeClosure) := by
  rw [negativeClosure_exact]
  exact wb_neg_closureCondition

#print axioms wb_actualPositiveClosure
#print axioms wb_neg_actualNegativeClosure
#print axioms wb_closurePositive
#print axioms wb_neg_closureCondition
end PA196InductionClosureWitness
