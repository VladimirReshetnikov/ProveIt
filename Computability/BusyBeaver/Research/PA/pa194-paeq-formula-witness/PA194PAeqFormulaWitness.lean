import PA194PAeqTermWitness

/-! The arithmetic-language formula recognizer's two witness bounds reduce to
corresponding term-vector recognizer bounds. The latter remain hypotheses. -/
set_option autoImplicit false
namespace PA194PAeqFormulaWitness
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.PRAFiniteFunctionCodes
open DiophantineConsistency.PRALanguage DiophantineConsistency.PRATheory
open DiophantineConsistency.PRAWitnessCalculus DiophantineConsistency.PRAWitnessArithmetic
open PA194PAeqAlphabetBounds

variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem wb_coreSigma (hv : WB M (isUTermVec PA194PAeq.language).sigma.val) :
    WB M (FormalizedFormula.blueprint PA194PAeq.language).core.sigma.val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := DiophantineConsistency.PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := hv; have := wb_qqRelDef (M := M); have := wb_qqNRelDef (M := M)
  have := wb_qqVerumDef (M := M); have := wb_qqFalsumDef (M := M); have := wb_qqAndDef (M := M)
  have := wb_qqOrDef (M := M); have := wb_qqAllDef (M := M); have := wb_qqExsDef (M := M)
  have := wb_bitDef (M := M); have := wb_isRel (M := M)
  simp only [FormalizedFormula.blueprint, FormalizedFormula.formulaAux,
    HierarchySymbol.Semiformula.sigma_mkDelta, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_coreNegPi (hv : WB M (∼(isUTermVec PA194PAeq.language).pi.val)) :
    WB M (∼(FormalizedFormula.blueprint PA194PAeq.language).core.pi.val) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := DiophantineConsistency.PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := hv; have := wb_qqRelDef (M := M); have := wb_qqNRelDef (M := M)
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

theorem wb_isUFormula_sigma (hs : WB M (isUTermVec PA194PAeq.language).sigma.val)
    (hp : WB M (∼(isUTermVec PA194PAeq.language).pi.val)) : WB M (isUFormula PA194PAeq.language).sigma.val :=
  DiophantineConsistency.PRAHistoryTruncation.wb_fixpoint_sigma _ (wb_coreSigma hs) (wb_coreNegPi hp)

theorem wb_isUFormula_neg_pi (hs : WB M (isUTermVec PA194PAeq.language).sigma.val)
    (hp : WB M (∼(isUTermVec PA194PAeq.language).pi.val)) : WB M (∼(isUFormula PA194PAeq.language).pi.val) :=
  DiophantineConsistency.PRAHistoryTruncation.wb_fixpoint_neg_pi _ (wb_coreSigma hs) (wb_coreNegPi hp)

theorem wb_formula_sigma_complete : WB M (isUFormula PA194PAeq.language).sigma.val :=
  wb_isUFormula_sigma PA194PAeqTermWitness.wb_isUTermVec_sigma PA194PAeqTermWitness.wb_isUTermVec_neg_pi

theorem wb_formula_neg_pi_complete : WB M (∼(isUFormula PA194PAeq.language).pi.val) :=
  wb_isUFormula_neg_pi PA194PAeqTermWitness.wb_isUTermVec_sigma PA194PAeqTermWitness.wb_isUTermVec_neg_pi

#print axioms wb_formula_sigma_complete
#print axioms wb_formula_neg_pi_complete
#print axioms wb_isUFormula_sigma
#print axioms wb_isUFormula_neg_pi
end PA194PAeqFormulaWitness
