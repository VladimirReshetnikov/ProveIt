import DiophantineConsistency.PRAWitnessPR
import Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1

/-! Bounded-witness results for the free-variable-vector component of
Foundation's induction-schema recognizer. No full recognizer bound is claimed. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace PA196InductionFvarWitness
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

/-- The fvar-vector graph under the recognizer's `fv`, `b`, `m`, `p` binders. -/
noncomputable def fvarGraph : ArithmeticSemisentence 4 :=
  Rewriting.subst fvarVecDef.val ![#0,#2]

/-- Extract that exact graph from the positive induction recognizer. -/
noncomputable def actualFvarGraph : ArithmeticSemisentence 4 :=
  match chUniv.sigma.val with
  | .exs (.and _ (.exs (.and _ (.and _ (.and _ (.and _ (.and _ (.exs (.and graph _))))))))) => graph
  | _ => ⊥

/-- Extract the actual existential and its residual conjunct from the same
recognizer. The residual conjunct still contains the substitution graph. -/
noncomputable def actualFvarExists : ArithmeticSemisentence 3 :=
  match chUniv.sigma.val with
  | .exs (.and _ (.exs (.and _ (.and _ (.and _ (.and _ (.and _ body))))))) => body
  | _ => ⊥

noncomputable def actualFvarTail : ArithmeticSemisentence 4 :=
  match chUniv.sigma.val with
  | .exs (.and _ (.exs (.and _ (.and _ (.and _ (.and _ (.and _ (.exs (.and _ tail))))))))) => tail
  | _ => ⊥

theorem fvarExists_exact : actualFvarExists = ∃⁰ (fvarGraph ⋏ actualFvarTail) := by rfl

theorem fvarGraph_exact : actualFvarGraph = fvarGraph := by rfl

theorem wb_actualFvarGraph : WB M actualFvarGraph := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := DiophantineConsistency.PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  rw [fvarGraph_exact]
  unfold fvarGraph
  exact wb_rew _ (wb_fvarVecDef (M := M))

/-- The recognizer's existential `fv` can be bounded while preserving any
remaining conjunct whose own witness bound is known. The three parameters are
`b`, `m`, and `p`, as in the actual recognizer. -/
theorem wb_exists_fvar_with_tail (tail : ArithmeticSemisentence 4) (hsigma : Hierarchy 𝚺 1 tail) (htail : WB M tail) :
    WB M (∃⁰ (fvarGraph ⋏ tail)) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := DiophantineConsistency.PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_fvarVecDef (M := M)
  unfold fvarGraph
  refine wb_exs_bt' _ (by simp [hsigma]) (tauT (poly ‘(#1 + 2) * (#1 + 2) + 1’) (poly ‘2 * #1’))
    (fun V _ _ e x h => ⟨x, ?_, h⟩) ?_
  · have h' := h; simp at h'
    rw [h'.1]; simpa [vval_tauT, vval] using fvarVec_le (e 1) (e 1) le_rfl
  · wb_auto

/-- The exact residual tail has the required syntactic Σ₁ complexity. -/
theorem actualFvarTail_sigma : Hierarchy 𝚺 1 actualFvarTail := by
  simp [actualFvarTail, chUniv, Semiformula.bexsLT, FirstOrder.bexs]

/-- Binding the generic step to the exact recognizer retains only the
remaining tail witness-bound obligation. -/
theorem wb_actualFvarExists (htail : WB M actualFvarTail) : WB M actualFvarExists := by
  rw [fvarExists_exact]
  exact wb_exists_fvar_with_tail actualFvarTail actualFvarTail_sigma htail

#print axioms actualFvarTail_sigma
#print axioms wb_actualFvarExists
#print axioms wb_actualFvarGraph
#print axioms wb_exists_fvar_with_tail
end PA196InductionFvarWitness
