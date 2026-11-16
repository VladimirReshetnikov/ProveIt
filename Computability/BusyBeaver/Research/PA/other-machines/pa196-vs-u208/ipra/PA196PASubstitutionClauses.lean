import PA196PAQVecGraph

/-! The ten positive clause bounds for arithmetic formula substitution.
Negative clauses and the global recursion-stage bound remain separate. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace PA196PASubstitutionClauses
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAWitnessCalculus PRAWitnessArithmetic
open PRAWitnessTransfer

variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem positive_clauses :
    WB M (Substs.blueprint ℒₒᵣ).rel.val ∧ WB M (Substs.blueprint ℒₒᵣ).nrel.val ∧
    WB M (Substs.blueprint ℒₒᵣ).verum.val ∧ WB M (Substs.blueprint ℒₒᵣ).falsum.val ∧
    WB M (Substs.blueprint ℒₒᵣ).and.val ∧ WB M (Substs.blueprint ℒₒᵣ).or.val ∧
    WB M (Substs.blueprint ℒₒᵣ).all.val ∧ WB M (Substs.blueprint ℒₒᵣ).exs.val ∧
    WB M (Substs.blueprint ℒₒᵣ).allChanges.val ∧ WB M (Substs.blueprint ℒₒᵣ).exsChanges.val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_qqRelDef (M := M); have := wb_qqNRelDef (M := M); have := wb_qqVerumDef (M := M)
  have := wb_qqFalsumDef (M := M); have := wb_qqAndDef (M := M); have := wb_qqOrDef (M := M)
  have := wb_qqAllDef (M := M); have := wb_qqExsDef (M := M)
  have := PA196PATermOperations.wb_termSubstVecGraph (M := M); have := PA196PAQVecGraph.wb_qVecGraph (M := M)
  have h_rel : WB M (Substs.blueprint ℒₒᵣ).rel.val := by
    simp only [Substs.blueprint, HierarchySymbol.Semiformula.val_mkSigma]
    exact PRAWitnessTransfer.wb_exs_poly _ (by simp) ‘#0’
      (fun V _ _ e u h => ⟨u, by
        have h' := h; simp at h'
        simpa [h'.2] using le_of_lt (v_lt_rel (e 2) (e 3) u), h⟩) (by wb_auto)
  have h_nrel : WB M (Substs.blueprint ℒₒᵣ).nrel.val := by
    simp only [Substs.blueprint, HierarchySymbol.Semiformula.val_mkSigma]
    exact PRAWitnessTransfer.wb_exs_poly _ (by simp) ‘#0’
      (fun V _ _ e u h => ⟨u, by
        have h' := h; simp at h'
        simpa [h'.2] using le_of_lt (v_lt_nrel (e 2) (e 3) u), h⟩) (by wb_auto)
  have ⟨h_verum, h_falsum, h_and, h_or, h_all, h_exs, h_allChanges, h_exsChanges⟩ :
      WB M (Substs.blueprint ℒₒᵣ).verum.val ∧ WB M (Substs.blueprint ℒₒᵣ).falsum.val ∧
      WB M (Substs.blueprint ℒₒᵣ).and.val ∧ WB M (Substs.blueprint ℒₒᵣ).or.val ∧
      WB M (Substs.blueprint ℒₒᵣ).all.val ∧ WB M (Substs.blueprint ℒₒᵣ).exs.val ∧
      WB M (Substs.blueprint ℒₒᵣ).allChanges.val ∧ WB M (Substs.blueprint ℒₒᵣ).exsChanges.val := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Substs.blueprint, HierarchySymbol.Semiformula.val_mkSigma] <;> wb_auto
  exact ⟨h_rel, h_nrel, h_verum, h_falsum, h_and, h_or, h_all, h_exs, h_allChanges, h_exsChanges⟩

#print axioms positive_clauses
end PA196PASubstitutionClauses
