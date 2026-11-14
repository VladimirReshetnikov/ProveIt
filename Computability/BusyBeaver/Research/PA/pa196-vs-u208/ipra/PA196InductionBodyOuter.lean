import PA196InductionBodyImp

/-! Conditional full induction-body graph witness bound. The exact arithmetic
substitution-graph witness bound and two numeric growth inequalities are
explicit hypotheses; the remaining four graph steps have been established. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace PA196InductionBodyOuter
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.PRAFiniteFunctionCodes DiophantineConsistency.PRALanguage
open DiophantineConsistency.PRATheory DiophantineConsistency.PRAWitnessCalculus
open DiophantineConsistency.PRAWitnessTransfer DiophantineConsistency.PRAWitnessBoundTerms
open DiophantineConsistency.PRAWitnessBoundTerms.BoundTerm
open DiophantineConsistency.PRAWitnessCodeGrowth

/-- Numeric growth of the two fixed substitution operations in all IΣ₁
models. The actual inequalities are not proved here. -/
def FixedSubstitutionGrowth : Prop :=
  ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V),
    subst ℒₒᵣ (indSubstConst0 : V) k ≤ tau ((indSubstConst0 : V) + k + 8) (4*k + 6) ∧
    subst ℒₒᵣ (indSubstConst1 : V) k ≤ tau ((indSubstConst1 : V) + k + 8) (4*k + 6)

variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

/-- Exactly the remaining substitutions suffice for the complete graph. -/
theorem wb_bodyGraph_of_substitution
    (hsub : WB M (substsGraph ℒₒᵣ).val) (hgrowth : FixedSubstitutionGrowth) :
    WB M indBodyValGraph.val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := DiophantineConsistency.PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := PA196InductionBodyImp.wb_actualImpExists (M := M)
  simp only [indBodyValGraph, HierarchySymbol.Semiformula.val_mkSigma]
  refine wb_exs_bt _ (by simp) (tauT (poly ‘↑indSubstConst0 + #1 + 8’) (poly ‘4 * #1 + 6’))
    (fun V _ _ e x h => by
      have h' := h; simp at h'
      rw [h'.1]
      simpa [vval_tauT, vval, numeral_eq_natCast] using (hgrowth V (e 1)).1) ?_
  wb_auto
  refine wb_exs_bt _ (by simp) (tauT (poly ‘↑indSubstConst1 + #2 + 8’) (poly ‘4 * #2 + 6’))
    (fun V _ _ e x h => by
      have h' := h; simp at h'
      rw [h'.1]
      simpa [vval_tauT, vval, numeral_eq_natCast] using (hgrowth V (e 2)).2) ?_
  wb_auto
  exact PA196InductionBodyImp.wb_actualImpExists

#print axioms wb_bodyGraph_of_substitution
end PA196InductionBodyOuter
