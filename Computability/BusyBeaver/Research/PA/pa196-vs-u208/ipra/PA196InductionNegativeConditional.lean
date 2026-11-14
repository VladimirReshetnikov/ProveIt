import PA196InductionFvarTailComplete
import PA196PAShiftGraphComplete

/-! Decomposition of the negative universal-induction recognizer. Explicit
counterexample bounds are required for its universal graph clauses. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
namespace PA196InductionNegativeConditional
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAWitnessCalculus PRAWitnessPR
  PRAWitnessBoundTerms PRAWitnessBoundTerms.BoundTerm PRAWitnessTransfer
  PA196PRAWitnessTower PA196PASubstitutionTotalGrowth

variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

def shiftCounterexample : ArithmeticSemisentence 3 :=
  ∃⁰ (Rewriting.subst (shiftGraph ℒₒᵣ).val ![#0,#1] ⋏
    Semiformula.nrel Language.ORing.Rel.eq ![#0,#1])
def bvCounterexample : ArithmeticSemisentence 3 :=
  ∃⁰ (Rewriting.subst (bvGraph ℒₒᵣ).val ![#0,#1] ⋏
    Semiformula.nrel Language.ORing.Rel.eq ![#0,#2])
def bodyCounterexample (n : ℕ) : ArithmeticSemisentence (n + 2) :=
  ∃⁰ (Rewriting.subst indBodyValGraph.val ![#0,#1] ⋏
    Semiformula.nrel Language.ORing.Rel.eq ![#2,#0])

theorem wb_negative (hshiftCounter : WB M shiftCounterexample)
    (hbvCounter : WB M bvCounterexample)
    (hbodyCounter : ∀ n, WB M (bodyCounterexample n)) : WB M (∼chUniv.pi.val) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_qqAllsDef (M := M)
  have := PA196PAFormulaComplete.wb_isUFormula_neg_pi (M := M)
  have := PA196PAShiftGraphComplete.wb_shiftGraph (M := M)
  have := PA196PAFormulaSetComplete.wb_bvGraph (M := M)
  have := wb_fvarVecDef (M := M)
  have := PA196PASubstitutionWitnessComplete.wb_substsGraph (M := M)
  have := PA196PAFormulaSetBound.wb_isSemiformula_neg_pi PA196PAFormulaSetComplete.wb_bvGraph (M := M)
  have := PA196InductionBodyComplete.wb_bodyGraph (M := M)
  simp only [chUniv, HierarchySymbol.Semiformula.pi_mkDelta,
    HierarchySymbol.Semiformula.val_mkPi]
  wb_auto
  · exact wb_exs_bt _ (by simp) (tauT (poly ‘#0’) (poly ‘2 * #1’)) (fun V _ _ e x h => by
      have h' := h; simp at h'
      rw [h'.1]; simpa [vval_tauT, vval] using qqAlls_le (e 0) (e 1)) (by wb_auto)
  · exact hshiftCounter
  · exact hbvCounter
  refine wb_exs_bt' _ (by simp) (tauT (poly ‘(#1 + 2) * (#1 + 2) + 1’) (poly ‘2 * #1’))
    (fun V _ _ e x h => ⟨x, ?_, h⟩) ?_
  · have h' := h; simp at h'
    rw [h'.1]; simpa [vval_tauT, vval] using fvarVec_le (e 1) (e 1) le_rfl
  wb_auto
  refine wb_exs_towerPoly _ (by simp) ‘#1 + #0’ ?_ ?_
  · intro V _ _ e x h
    refine ⟨x, ?_, h⟩
    have h' := h
    simp at h'
    rw [h'.1]
    simpa [Semiterm.val_func, numeral_eq_natCast] using subst_le_tower (e 0) (e 1)
  · wb_auto
    exact hbodyCounter _

#print axioms wb_negative
end PA196InductionNegativeConditional
