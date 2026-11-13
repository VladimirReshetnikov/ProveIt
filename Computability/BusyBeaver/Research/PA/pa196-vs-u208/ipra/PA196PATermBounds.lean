import PA196PAAlphabetBounds

/-! Arithmetic-language term and term-vector recognizer witness bounds, in
both polarities. This checks their actual Foundation definitions in every
classical PRA model in the primitive-recursive language. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace PA196PATermBounds
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.PRAFiniteFunctionCodes
open DiophantineConsistency.PRALanguage DiophantineConsistency.PRATheory
open DiophantineConsistency.PRAWitnessCalculus DiophantineConsistency.PRAWitnessArithmetic
open DiophantineConsistency.PRAWitnessVectors DiophantineConsistency.PRAWitnessTransfer
open PA196PAAlphabetBounds

variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem wb_coreSigma : WB M (FormalizedTerm.blueprint ℒₒᵣ).core.sigma.val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := DiophantineConsistency.PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_qqBvarDef (M := M); have := wb_qqFvarDef (M := M)
  have := wb_qqFuncDef (M := M); have := wb_isFunc (M := M)
  have := wb_lenDef (M := M); have := wb_nthDef (M := M); have := wb_bitDef (M := M)
  simp only [FormalizedTerm.blueprint, HierarchySymbol.Semiformula.sigma_mkDelta,
    HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto
  exact wb_exs_poly _ (by simp) ‘#1’
    (fun V _ _ e u h => ⟨u, by have h' := h; simp at h'; simp [h'.1], h⟩) (by wb_auto)

theorem wb_coreNegPi : WB M (∼(FormalizedTerm.blueprint ℒₒᵣ).core.pi.val) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := DiophantineConsistency.PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_neg_qqBvarDef (M := M); have := wb_neg_qqFvarDef (M := M)
  have := wb_neg_qqFuncDef (M := M); have := wb_neg_isFunc (M := M)
  have := wb_lenDef (M := M); have := wb_nthDef (M := M); have := wb_neg_bitDef (M := M)
  simp only [FormalizedTerm.blueprint, HierarchySymbol.Semiformula.pi_mkDelta,
    HierarchySymbol.Semiformula.val_mkPi]
  wb_auto
  · exact wb_exs_poly _ (by simp) ‘#0’
      (fun V _ _ e l h => ⟨l, by have h' := h; simp at h'; simp [h'.1], h⟩) (by wb_auto)
  · exact wb_exs_poly _ (by simp) ‘#1’
      (fun V _ _ e u h => ⟨u, by have h' := h; simp at h'; simp [h'.1], h⟩) (by wb_auto)

theorem wb_isUTerm_sigma : WB M (isUTerm ℒₒᵣ).sigma.val :=
  DiophantineConsistency.PRAHistoryTruncation.wb_fixpoint_sigma _ wb_coreSigma wb_coreNegPi

theorem wb_isUTerm_neg_pi : WB M (∼(isUTerm ℒₒᵣ).pi.val) :=
  DiophantineConsistency.PRAHistoryTruncation.wb_fixpoint_neg_pi _ wb_coreSigma wb_coreNegPi

theorem wb_isUTermVec_sigma : WB M (isUTermVec ℒₒᵣ).sigma.val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := DiophantineConsistency.PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_lenDef (M := M); have := wb_nthDef (M := M); have := wb_isUTerm_sigma (M := M)
  simp only [isUTermVec, HierarchySymbol.Semiformula.sigma_mkDelta, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto
  exact wb_exs_poly _ (by simp) ‘#2’
    (fun V _ _ e u h => ⟨u, by have h' := h; simp at h'; simp [h'.1], h⟩) (by wb_auto)

theorem wb_isUTermVec_neg_pi : WB M (∼(isUTermVec ℒₒᵣ).pi.val) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := DiophantineConsistency.PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_lenDef (M := M); have := wb_nthDef (M := M); have := wb_isUTerm_neg_pi (M := M)
  simp only [isUTermVec, HierarchySymbol.Semiformula.pi_mkDelta, HierarchySymbol.Semiformula.val_mkPi]
  wb_auto
  · exact wb_exs_poly _ (by simp) ‘#1’
      (fun V _ _ e l h => ⟨l, by have h' := h; simp at h'; simp [h'.1], h⟩) (by wb_auto)
  · exact wb_exs_poly _ (by simp) ‘#2’
      (fun V _ _ e u h => ⟨u, by have h' := h; simp at h'; simp [h'.1], h⟩) (by wb_auto)

#print axioms wb_isUTerm_sigma
#print axioms wb_isUTerm_neg_pi
#print axioms wb_isUTermVec_sigma
#print axioms wb_isUTermVec_neg_pi
end PA196PATermBounds
