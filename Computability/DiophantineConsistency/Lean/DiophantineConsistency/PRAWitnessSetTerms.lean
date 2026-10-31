import DiophantineConsistency.PRAWitnessVectors
import ZFCinPA.Instances
/-! # Witness bounds for the terms of `ℒₛₑₜ`

`ℒₛₑₜ` has no function symbols (`isFunc` is literally `⊥`), so its terms are
variables. The term-recognition fixpoint is strong-finite (Foundation), its
core's function branch collapses to `⊥ ⋏ …`, and `PRAHistoryTruncation` gives
witness bounds for both polarities of `isUTerm`. Term vectors (`isUTermVec`)
add `len` and `nth`, whose values are bounded by the vector in `𝗜𝚺₁`
(`len_le`, `nth_le`); `PRAWitnessTransfer.wb_exs_poly` moves those bounds to
candidate PRA. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAWitnessSetTerms
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open StrictSigmaOneInduction PRAWitnessCalculus PRAWitnessArithmetic PRAWitnessVectors

theorem func_def_set : (ℒₛₑₜ).isFunc = .mkSigma “k f. ⊥” := rfl

section sigma1
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem not_isFunc (k f : V) : ¬(ℒₛₑₜ).IsFunc k f := by
  simp [Language.IsFunc, func_def_set]

/-- Over `ℒₛₑₜ` a term-recursion core never queries its argument set: function
terms are not terms. -/
theorem termRec_set_rankFinite {β : Language.TermRec.Blueprint 0}
    (c : Language.TermRec.Construction V β) :
    PRAFixpointRank.RankFinite (c.construction ℒₛₑₜ) (fun x => x) := by
  intro v C x h
  simp only [Language.TermRec.Construction.construction, Language.TermRec.Construction.Phi] at h ⊢
  rcases h with ⟨ht, (h | h | ⟨k, f, w, w', hw, hx⟩)⟩
  · exact ⟨ht, Or.inl h⟩
  · exact ⟨ht, Or.inr (Or.inl h)⟩
  · exfalso
    rw [hx] at ht
    exact not_isFunc k f (IsUTerm.func_iff.mp (by simpa using ht)).1

end sigma1

section models
open PRAFiniteFunctionCodes PRALanguage PRATheory
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem wb_uterm_core_sigma : WB M (FormalizedTerm.blueprint ℒₛₑₜ).core.sigma.val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_qqBvarDef (M := M); have := wb_qqFvarDef (M := M)
  simp only [FormalizedTerm.blueprint, HierarchySymbol.Semiformula.sigma_mkDelta,
    HierarchySymbol.Semiformula.val_mkSigma, func_def_set, subst_bot]
  wb_auto

theorem wb_uterm_core_neg_pi : WB M (∼(FormalizedTerm.blueprint ℒₛₑₜ).core.pi.val) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_neg_qqBvarDef (M := M); have := wb_neg_qqFvarDef (M := M)
  simp only [FormalizedTerm.blueprint, HierarchySymbol.Semiformula.pi_mkDelta,
    HierarchySymbol.Semiformula.val_mkPi, HierarchySymbol.Semiformula.val_mkSigma, func_def_set]
  wb_auto

theorem wb_isUTerm_sigma : WB M (isUTerm ℒₛₑₜ).sigma.val :=
  PRAHistoryTruncation.wb_fixpoint_sigma _ wb_uterm_core_sigma wb_uterm_core_neg_pi

theorem wb_isUTerm_neg_pi : WB M (∼(isUTerm ℒₛₑₜ).pi.val) :=
  PRAHistoryTruncation.wb_fixpoint_neg_pi _ wb_uterm_core_sigma wb_uterm_core_neg_pi

theorem wb_isUTermVec_sigma : WB M (isUTermVec ℒₛₑₜ).sigma.val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_lenDef (M := M); have := wb_nthDef (M := M); have := wb_isUTerm_sigma (M := M)
  simp only [isUTermVec, HierarchySymbol.Semiformula.sigma_mkDelta, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto
  exact PRAWitnessTransfer.wb_exs_poly _ (by simp) ‘#2’
    (fun V _ _ e u h => ⟨u, by have h' := h; simp at h'; simp [h'.1], h⟩) (by wb_auto)

theorem wb_isUTermVec_neg_pi : WB M (∼(isUTermVec ℒₛₑₜ).pi.val) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_lenDef (M := M); have := wb_nthDef (M := M); have := wb_isUTerm_neg_pi (M := M)
  simp only [isUTermVec, HierarchySymbol.Semiformula.pi_mkDelta, HierarchySymbol.Semiformula.val_mkPi]
  wb_auto
  · exact PRAWitnessTransfer.wb_exs_poly _ (by simp) ‘#1’
      (fun V _ _ e l h => ⟨l, by have h' := h; simp at h'; simp [h'.1], h⟩) (by wb_auto)
  · exact PRAWitnessTransfer.wb_exs_poly _ (by simp) ‘#2’
      (fun V _ _ e u h => ⟨u, by have h' := h; simp at h'; simp [h'.1], h⟩) (by wb_auto)

end models
end DiophantineConsistency.PRAWitnessSetTerms
