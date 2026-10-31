import DiophantineConsistency.PRAWitnessCodeGrowth
/-! # Witness bounds for substitution over `ℒₛₑₜ`

`subst` is a formula recursion whose parameter grows at quantifiers
(`qVec`), so `PRAWitnessFormulaRec.recRank` does not decrease along it.
Its fixpoint stage is instead bounded directly in `𝗜𝚺₁`
(`PRAWitnessCodeGrowth.subst_fixpoint_stage`), and
`PRAWitnessFormulaRec.wb_fixpointDef_exp` moves that bound to candidate
PRA. `substs1` and `free` follow. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAWitnessSubsts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open StrictSigmaOneInduction PRAWitnessCalculus PRAWitnessArithmetic PRAWitnessVectors PRAWitnessSetTerms
  PRAWitnessTermRec PRAWitnessTermFunctions PRAWitnessFormulas PRAWitnessFormulaRec PRAWitnessRepeatVec
  PRAWitnessExpBounds PRAWitnessFormulaFunctions PRAWitnessCodeGrowth

section models
open PRAFiniteFunctionCodes PRALanguage PRATheory
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem subst_clauses : PRAWitnessFormulaRec.ClauseBounds (Substs.blueprint ℒₛₑₜ) M := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_qqRelDef (M := M); have := wb_qqNRelDef (M := M); have := wb_qqVerumDef (M := M)
  have := wb_qqFalsumDef (M := M); have := wb_qqAndDef (M := M); have := wb_qqOrDef (M := M)
  have := wb_qqAllDef (M := M); have := wb_qqExsDef (M := M)
  have := wb_termSubstVecGraph (M := M); have := wb_qVecGraph (M := M)
  have h_rel : WB M (Substs.blueprint ℒₛₑₜ).rel.val := by
    simp only [Substs.blueprint, HierarchySymbol.Semiformula.val_mkSigma]
    exact PRAWitnessTransfer.wb_exs_poly _ (by simp) ‘#0’
      (fun V _ _ e u h => ⟨u, by
        have h' := h; simp at h'
        simpa [h'.2] using le_of_lt (v_lt_rel (e 2) (e 3) u), h⟩) (by wb_auto)
  have h_nrel : WB M (Substs.blueprint ℒₛₑₜ).nrel.val := by
    simp only [Substs.blueprint, HierarchySymbol.Semiformula.val_mkSigma]
    exact PRAWitnessTransfer.wb_exs_poly _ (by simp) ‘#0’
      (fun V _ _ e u h => ⟨u, by
        have h' := h; simp at h'
        simpa [h'.2] using le_of_lt (v_lt_nrel (e 2) (e 3) u), h⟩) (by wb_auto)
  have h_verum : WB M (Substs.blueprint ℒₛₑₜ).verum.val := by
    simp only [Substs.blueprint, HierarchySymbol.Semiformula.val_mkSigma]; wb_auto
  have h_falsum : WB M (Substs.blueprint ℒₛₑₜ).falsum.val := by
    simp only [Substs.blueprint, HierarchySymbol.Semiformula.val_mkSigma]; wb_auto
  have h_and : WB M (Substs.blueprint ℒₛₑₜ).and.val := by
    simp only [Substs.blueprint, HierarchySymbol.Semiformula.val_mkSigma]; wb_auto
  have h_or : WB M (Substs.blueprint ℒₛₑₜ).or.val := by
    simp only [Substs.blueprint, HierarchySymbol.Semiformula.val_mkSigma]; wb_auto
  have h_all : WB M (Substs.blueprint ℒₛₑₜ).all.val := by
    simp only [Substs.blueprint, HierarchySymbol.Semiformula.val_mkSigma]; wb_auto
  have h_exs : WB M (Substs.blueprint ℒₛₑₜ).exs.val := by
    simp only [Substs.blueprint, HierarchySymbol.Semiformula.val_mkSigma]; wb_auto
  have h_allChanges : WB M (Substs.blueprint ℒₛₑₜ).allChanges.val := by
    simp only [Substs.blueprint, HierarchySymbol.Semiformula.val_mkSigma]; wb_auto
  have h_exsChanges : WB M (Substs.blueprint ℒₛₑₜ).exsChanges.val := by
    simp only [Substs.blueprint, HierarchySymbol.Semiformula.val_mkSigma]; wb_auto
  refine ⟨h_rel, h_nrel, h_verum, h_falsum, h_and, h_or, h_all, h_exs, h_allChanges, h_exsChanges,
    wb_neg_graphDelta_pi_exp _ h_rel ‘#3 + #0 + #1 + #2 + 1 + 2’ ‘2 * (#1 + 1 + 1 + 1)’ ?_,
    wb_neg_graphDelta_pi_exp _ h_nrel ‘#3 + #0 + #1 + #2 + 1 + 2’ ‘2 * (#1 + 1 + 1 + 1)’ ?_,
    wb_neg_graphDelta_pi _ h_verum ‘(2 + 0 + 1) * (2 + 0 + 1) + 1’ ?_,
    wb_neg_graphDelta_pi _ h_falsum ‘(3 + 0 + 1) * (3 + 0 + 1) + 1’ ?_,
    wb_neg_graphDelta_pi _ h_and ‘(4 + (#3 + #4 + 1) * (#3 + #4 + 1) + 1) * (4 + (#3 + #4 + 1) * (#3 + #4 + 1) + 1) + 1’ ?_,
    wb_neg_graphDelta_pi _ h_or ‘(5 + (#3 + #4 + 1) * (#3 + #4 + 1) + 1) * (5 + (#3 + #4 + 1) * (#3 + #4 + 1) + 1) + 1’ ?_,
    wb_neg_graphDelta_pi _ h_all ‘(6 + #2 + 1) * (6 + #2 + 1) + 1’ ?_,
    wb_neg_graphDelta_pi _ h_exs ‘(7 + #2 + 1) * (7 + #2 + 1) + 1’ ?_,
    ?_, ?_⟩
  · intro V _ _ e y h
    simp [Substs.blueprint] at h
    rw [h]
    have hm : e 3 + e 0 ≤ e 3 + e 0 + e 1 + e 2 + 1 := le_trans (le_trans le_self_add le_self_add) le_self_add
    have hv := le_trans (termSubstVec_le (e 1) (e 0) (e 3)) (repeatVec_mono_left hm (e 1))
    have hy := code4_le_repeatVec (c := 0) (by simp)
      (le_trans (le_trans le_add_self le_self_add) le_self_add) (le_trans le_add_self le_self_add) hv
    have := le_trans hy (le_of_lt (repeatVec_lt _ _))
    simpa [qqRel, numeral_eq_natCast] using this
  · intro V _ _ e y h
    simp [Substs.blueprint] at h
    rw [h]
    have hm : e 3 + e 0 ≤ e 3 + e 0 + e 1 + e 2 + 1 := le_trans (le_trans le_self_add le_self_add) le_self_add
    have hv := le_trans (termSubstVec_le (e 1) (e 0) (e 3)) (repeatVec_mono_left hm (e 1))
    have hy := code4_le_repeatVec (c := 1) le_add_self
      (le_trans (le_trans le_add_self le_self_add) le_self_add) (le_trans le_add_self le_self_add) hv
    have := le_trans hy (le_of_lt (repeatVec_lt _ _))
    simpa [qqNRel, numeral_eq_natCast] using this
  · intro V _ _ e y h; simp [Substs.blueprint] at h; rw [h]; simpa [qqVerum, numeral_eq_natCast] using code2_le (2 : V) 0
  · intro V _ _ e y h; simp [Substs.blueprint] at h; rw [h]; simpa [qqFalsum, numeral_eq_natCast] using code2_le (3 : V) 0
  · intro V _ _ e y h; simp [Substs.blueprint] at h; rw [h]; simpa [qqAnd, numeral_eq_natCast] using code3_le 4 (e 3) (e 4)
  · intro V _ _ e y h; simp [Substs.blueprint] at h; rw [h]; simpa [qqOr, numeral_eq_natCast] using code3_le 5 (e 3) (e 4)
  · intro V _ _ e y h; simp [Substs.blueprint] at h; rw [h]; simpa [qqAll, numeral_eq_natCast] using code2_le 6 (e 2)
  · intro V _ _ e y h; simp [Substs.blueprint] at h; rw [h]; simpa [qqExs, numeral_eq_natCast] using code2_le 7 (e 2)
  · intro V _ _ a b h; simp [Substs.blueprint] at h; rw [h]; simpa [tau] using qVec_le b
  · intro V _ _ a b h; simp [Substs.blueprint] at h; rw [h]; simpa [tau] using qVec_le b

theorem wb_subst_fixpoint : WB M ((Substs.blueprint ℒₛₑₜ).blueprint ℒₛₑₜ).fixpointDef.val := by
  refine wb_fixpointDef_exp _ (wb_core_sigma subst_clauses) (wb_core_neg_pi subst_clauses)
    ‘#0 + #0 + 8 + 4’ ‘10 * #0 + 12’ ?_
  intro V _ _ e s L hL hx
  have hL' : L = substFix.limSeq ![] s := by
    simpa [Matrix.empty_eq] using (substFix.eval_limSeqDef (L :> s :> fun i => e i.succ)).mp hL
  have hxL : e 0 ∈ L := by simpa [Semiformula.Operator.val, operator_mem_def] using hx
  have hst := subst_fixpoint_stage (hL' ▸ hxL)
  refine ⟨substStage (tau (e 0 + e 0 + 8) (10 * e 0 + 12)), ?_, ?_⟩
  · have := (substFix.eval_limSeqDef
      (substStage (tau (e 0 + e 0 + 8) (10 * e 0 + 12)) :> tau (e 0 + e 0 + 8) (10 * e 0 + 12) :>
        fun i => e i.succ)).mpr (by simp [substStage, Matrix.empty_eq])
    simpa [tau, numeral_eq_natCast] using this
  · simpa [Semiformula.Operator.val, operator_mem_def] using hst

theorem substsGraph_eq : substsGraph ℒₛₑₜ = (Substs.blueprint ℒₛₑₜ).result ℒₛₑₜ := by
  unfold substsGraph; rfl

theorem wb_substsGraph : WB M (substsGraph ℒₛₑₜ).val := by
  rw [substsGraph_eq]; exact wb_result_of_fixpoint wb_subst_fixpoint

theorem wb_substs1Graph : WB M (substs1Graph ℒₛₑₜ).val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_substsGraph (M := M); have := wb_adjoinDef (M := M)
  simp only [substs1Graph, HierarchySymbol.Semiformula.val_mkSigma]
  exact PRAWitnessTransfer.wb_exs_poly _ (by simp) ‘(#1 + 1) * (#1 + 1) + 1’
    (fun V _ _ e u h => ⟨u, by
      have h' := h; simp at h'
      rw [h'.1, adjoin_def]
      simpa using add_le_add (pair_le_sq (le_refl (e 1)) (le_refl 0)) (le_refl 1), h⟩) (by wb_auto)

theorem wb_freeGraph : WB M (freeGraph ℒₛₑₜ).val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_substs1Graph (M := M); have := wb_shiftGraph (M := M); have := wb_qqFvarDef (M := M)
  simp only [freeGraph, HierarchySymbol.Semiformula.val_mkSigma]
  refine PRAWitnessTransfer.wb_exs_poly _ (by simp) ‘(1 + 0 + 1) * (1 + 0 + 1) + 1’
    (fun V _ _ e u h => ⟨u, by
      have h' := h; simp at h'
      rw [h'.1]; simpa [qqFvar] using code2_le (1 : V) 0, h⟩) ?_
  wb_auto
  refine PRAWitnessTransfer.wb_exs_bound _ (by simp)
    (expGraph2 ‘(#2 + 2) * (#2 + 2) + 1 + 8 + 4’ ‘2 * #2 + 6’)
    (expBound2 ‘(#2 + 2) * (#2 + 2) + 1 + 8 + 4’ ‘2 * #2 + 6’)
    (dominates_expBound2 _ _) (mono_expBound2 _ _) (fun V _ _ e x h => ?_) (by wb_auto)
  have h' := h; simp at h'
  refine ⟨Exp.exp (((e 2 + 2) * (e 2 + 2) + 1 + 8 + 4) * Exp.exp (2 * e 2 + 6)), ?_, x, ?_, h⟩
  · rw [eval_expGraph2]
    exact ⟨_, by simpa [numeral_eq_natCast] using exponential_exp (2 * e 2 + 6),
      by simpa [numeral_eq_natCast] using exponential_exp _⟩
  · rw [h'.1]
    by_cases hp : IsUFormula ℒₛₑₜ (e 2)
    · simpa [tau, numeral_eq_natCast] using shift_le (e 2) hp
    · simp [shift_not_uformula hp]

end models
end DiophantineConsistency.PRAWitnessSubsts
