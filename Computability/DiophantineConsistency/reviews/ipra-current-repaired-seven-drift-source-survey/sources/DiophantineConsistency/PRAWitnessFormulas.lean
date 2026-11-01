import DiophantineConsistency.PRAWitnessTermFunctions
/-! # Witness bounds for the formulas of `ℒₛₑₜ`

Formula recognition `isUFormula` is a strong-finite fixpoint; its core uses
the `𝚺₀` relation-symbol recognizer of `ℒₛₑₜ`, term vectors and the formula
codes, so `PRAHistoryTruncation` bounds both polarities. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAWitnessFormulas
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open StrictSigmaOneInduction PRAWitnessCalculus PRAWitnessArithmetic PRAWitnessVectors PRAWitnessSetTerms
  PRAWitnessTermRec PRAWitnessRepeatVec PRAWitnessExpBounds PRAWitnessTermFunctions

theorem rel_def_set : (ℒₛₑₜ).isRel = .mkSigma “k r. (k = 2 ∧ r = 0) ∨ (k = 2 ∧ r = 1)” := rfl

section models
open PRAFiniteFunctionCodes PRALanguage PRATheory
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem wb_isRel : WB M (ℒₛₑₜ).isRel.val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  rw [rel_def_set, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_neg_isRel : WB M (∼(ℒₛₑₜ).isRel.val) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  rw [rel_def_set, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_uformula_core_sigma : WB M (FormalizedFormula.blueprint ℒₛₑₜ).core.sigma.val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_isUTermVec_sigma (M := M); have := wb_qqRelDef (M := M); have := wb_qqNRelDef (M := M)
  have := wb_qqVerumDef (M := M); have := wb_qqFalsumDef (M := M); have := wb_qqAndDef (M := M)
  have := wb_qqOrDef (M := M); have := wb_qqAllDef (M := M); have := wb_qqExsDef (M := M)
  have := wb_bitDef (M := M); have := wb_isRel (M := M)
  simp only [FormalizedFormula.blueprint, FormalizedFormula.formulaAux,
    HierarchySymbol.Semiformula.sigma_mkDelta, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_uformula_core_neg_pi : WB M (∼(FormalizedFormula.blueprint ℒₛₑₜ).core.pi.val) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_isUTermVec_neg_pi (M := M); have := wb_qqRelDef (M := M); have := wb_qqNRelDef (M := M)
  have := wb_qqVerumDef (M := M); have := wb_qqFalsumDef (M := M); have := wb_qqAndDef (M := M)
  have := wb_qqOrDef (M := M); have := wb_qqAllDef (M := M); have := wb_qqExsDef (M := M)
  have := wb_bitDef (M := M); have := wb_isRel (M := M)
  have := wb_neg_qqRelDef (M := M); have := wb_neg_qqNRelDef (M := M)
  have := wb_neg_qqVerumDef (M := M); have := wb_neg_qqFalsumDef (M := M); have := wb_neg_qqAndDef (M := M)
  have := wb_neg_qqOrDef (M := M); have := wb_neg_qqAllDef (M := M); have := wb_neg_qqExsDef (M := M)
  have := wb_neg_bitDef (M := M); have := wb_neg_isRel (M := M)
  simp only [FormalizedFormula.blueprint, FormalizedFormula.formulaAux,
    HierarchySymbol.Semiformula.pi_mkDelta, HierarchySymbol.Semiformula.val_mkPi,
    HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_isUFormula_sigma : WB M (isUFormula ℒₛₑₜ).sigma.val :=
  PRAHistoryTruncation.wb_fixpoint_sigma _ wb_uformula_core_sigma wb_uformula_core_neg_pi

theorem wb_isUFormula_neg_pi : WB M (∼(isUFormula ℒₛₑₜ).pi.val) :=
  PRAHistoryTruncation.wb_fixpoint_neg_pi _ wb_uformula_core_sigma wb_uformula_core_neg_pi

end models
end DiophantineConsistency.PRAWitnessFormulas
