import DiophantineConsistency.PRAWitnessTermRec
/-! # Witness bounds for the term functions over `ℒₛₑₜ`

`listMax` is a vector recursion bounded by its argument. `termBV`, the
bound-variable bound, is the term recursion `IsUTerm.BV`; its clauses have
values bounded by their arguments, so `PRAWitnessTermRec` applies, and over
`ℒₛₑₜ` `termBV t ≤ t` bounds the unbounded `b` of `isSemiterm` and
`isSemitermVec` in both polarities. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAWitnessTermFunctions
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open StrictSigmaOneInduction PRAWitnessCalculus PRAWitnessArithmetic PRAWitnessVectors PRAWitnessSetTerms
  PRAWitnessTermRec

section sigma1
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem listMax_le_self (v : V) : listMax v ≤ v := listMaxss_le fun i _ => nth_le v i

/-- Over `ℒₛₑₜ` the bound-variable bound of a code is at most the code. -/
theorem termBV_le_self (t : V) : termBV ℒₛₑₜ t ≤ t := by
  by_cases ht : IsUTerm ℒₛₑₜ t
  · rcases IsUTerm.case ht with ⟨z, rfl⟩ | ⟨x, rfl⟩ | ⟨k, f, v, hkf, -, -⟩
    · simpa using lt_iff_succ_le.mp (var_lt_qqBvar z)
    · simp
    · exact absurd hkf (not_isFunc k f)
  · simp [termBV, IsUTerm.BV.construction, Language.TermRec.Construction.result_prop_not _ _ _ ht]

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

theorem wb_maxDef : WB M max.dfn.val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  simp only [max.dfn, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_listMax_core_sigma : WB M ListMax.blueprint.blueprint.core.sigma.val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_pairDef (M := M); have := wb_adjoinDef (M := M); have := wb_memRel (M := M)
  have := wb_maxDef (M := M)
  have : WB M memRelOpr.sentence := wb_memRel (M := M)
  simp only [VecRec.Blueprint.blueprint, ListMax.blueprint, HierarchySymbol.Semiformula.sigma_mkDelta,
    HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto
  · exact wb_exs_term ‘0’ (fun e y h => by simp at h; simp [h.1]) (by wb_auto)
  · refine wb_exs_term ‘(#2 + #1 + 1) * (#2 + #1 + 1) + 1’ (fun e y h => ?_) ?_
    · simp [adjoinDef] at h
      rw [h.1.2]
      have hp : ⟪e 2, e 1⟫ ≤ (e 2 + e 1 + 1) * (e 2 + e 1 + 1) := by
        simpa [sq] using pair_polybound (e 2) (e 1)
      simpa using add_le_add_right hp 1
    · refine wb_and (by wb_auto) (wb_exs_term ‘#3 + #1’ (fun e y h => ?_) (by wb_auto))
      simp at h
      rw [h.1]
      exact max_le le_self_add le_add_self

theorem wb_listMax_core_neg_pi : WB M (∼ListMax.blueprint.blueprint.core.pi.val) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_pairDef (M := M); have := wb_adjoinDef (M := M); have := wb_memRel (M := M)
  have := wb_maxDef (M := M)
  have := wb_neg_pairDef (M := M); have := wb_neg_memRel (M := M)
  have : WB M memRelOpr.sentence := wb_memRel (M := M)
  have : WB M (∼memRelOpr.sentence) := wb_neg_memRel (M := M)
  simp only [VecRec.Blueprint.blueprint, ListMax.blueprint, HierarchySymbol.Semiformula.pi_mkDelta,
    HierarchySymbol.Semiformula.val_mkPi, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto
  · exact wb_exs_term ‘0’ (fun e y h => by simp at h; simp [h.1]) (by wb_auto)
  · refine wb_exs_term ‘(#2 + #1 + 1) * (#2 + #1 + 1) + 1’ (fun e y h => ?_) ?_
    · simp [adjoinDef] at h
      rw [h.1.2]
      have hp : ⟪e 2, e 1⟫ ≤ (e 2 + e 1 + 1) * (e 2 + e 1 + 1) := by
        simpa [sq] using pair_polybound (e 2) (e 1)
      simpa using add_le_add_right hp 1
    · refine wb_and (by wb_auto) (wb_exs_term ‘#3 + #1’ (fun e y h => ?_) (by wb_auto))
      simp at h
      rw [h.1]
      exact max_le le_self_add le_add_self

/-- **`listMax`'s graph has bounded witnesses.** -/
theorem wb_listMax_graph : WB M ListMax.blueprint.graphDef.val := by
  refine PRAWitnessFixpointGraph.wb_fixpointDef ListMax.blueprint.blueprint wb_listMax_core_sigma
    wb_listMax_core_neg_pi ‘#0 + 1’ ?_
  intro V _ _ e s L hL hx
  have h := PRAWitnessFixpointGraph.stage_bound_of_rank
    (ListMax.adjointruction (V := V)).adjointruction (fun x => x) (fun _ => le_rfl)
    (vecRec_rankFinite ListMax.adjointruction (fun _ _ ih => le_max_right _ ih))
    (fun x => x + 1) (fun _ => le_rfl) (fun i => e i.succ) (e 0) s L hL hx
  exact ⟨_, by simpa using h.1, h.2⟩

/-- **`listMaxDef` has bounded witnesses.** -/
theorem wb_listMaxDef : WB M listMaxDef.val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have hg := wb_listMax_graph (M := M); have := wb_pairDef (M := M)
  simp only [listMaxDef, VecRec.Blueprint.resultDef, HierarchySymbol.Semiformula.val_mkSigma]
  refine wb_exs_term ‘(#1 + #0 + 1) * (#1 + #0 + 1)’ (fun e y h => ?_) (by wb_auto)
  simp at h
  rw [h.1]
  simpa [sq] using pair_polybound (e 1) (e 0)

/-! ### Bound-variable bound `termBV` -/

theorem bv_clauses : ClauseBounds IsUTerm.BV.blueprint M := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_listMaxDef (M := M)
  have hb : WB M IsUTerm.BV.blueprint.bvar.val := by
    simp only [IsUTerm.BV.blueprint, HierarchySymbol.Semiformula.val_mkSigma]; wb_auto
  have hf : WB M IsUTerm.BV.blueprint.fvar.val := by
    simp only [IsUTerm.BV.blueprint, HierarchySymbol.Semiformula.val_mkSigma]; wb_auto
  have hu : WB M IsUTerm.BV.blueprint.func.val := by
    simp only [IsUTerm.BV.blueprint, HierarchySymbol.Semiformula.val_mkSigma]; wb_auto
  refine ⟨hb, hf, hu, wb_neg_graphDelta_pi _ hb ‘#0 + 1’ ?_, wb_neg_graphDelta_pi _ hf ‘0’ ?_,
    wb_neg_graphDelta_pi _ hu ‘#3’ ?_⟩
  · intro V _ _ e y h; simp [IsUTerm.BV.blueprint] at h; simp [h]
  · intro V _ _ e y h; simp [IsUTerm.BV.blueprint] at h; simp [h]
  · intro V _ _ e y h; simp [IsUTerm.BV.blueprint] at h; simpa [h] using listMax_le_self (e 3)

/-- `termBV` in every `𝗜𝚺₁` model. -/
noncomputable abbrev bvConstructions : Constructions IsUTerm.BV.blueprint :=
  fun _ _ _ => IsUTerm.BV.construction

theorem wb_termBVGraph : WB M (termBVGraph ℒₛₑₜ).val :=
  wb_result bvConstructions bv_clauses

theorem wb_isSemiterm_sigma : WB M (isSemiterm ℒₛₑₜ).sigma.val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_termBVGraph (M := M); have := wb_isUTerm_sigma (M := M)
  simp only [isSemiterm, HierarchySymbol.Semiformula.sigma_mkDelta, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto
  exact wb_exs_term ‘#0’ (fun e y h => by simp at h; exact h.2) (by wb_auto)

theorem wb_isSemiterm_neg_pi : WB M (∼(isSemiterm ℒₛₑₜ).pi.val) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_termBVGraph (M := M); have := wb_isUTerm_neg_pi (M := M)
  simp only [isSemiterm, HierarchySymbol.Semiformula.pi_mkDelta, HierarchySymbol.Semiformula.val_mkPi]
  wb_auto
  exact PRAWitnessTransfer.wb_exs_poly _ (by simp) ‘#1’
    (fun V _ _ e b h => ⟨b, by
      have h' := h; simp at h'; rw [h'.1]; exact termBV_le_self (e 1), h⟩) (by wb_auto)

theorem wb_isSemitermVec_sigma : WB M (isSemitermVec ℒₛₑₜ).sigma.val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_termBVGraph (M := M); have := wb_isUTermVec_sigma (M := M); have := wb_nthDef (M := M)
  simp only [isSemitermVec, HierarchySymbol.Semiformula.sigma_mkDelta, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto
  exact PRAWitnessTransfer.wb_exs_poly _ (by simp) ‘#3’
    (fun V _ _ e u h => ⟨u, by have h' := h; simp at h'; simp [h'.1], h⟩)
    (by
      wb_auto
      exact wb_exs_term ‘#3’ (fun e y h => by simp at h; exact h.2) (by wb_auto))

theorem wb_isSemitermVec_neg_pi : WB M (∼(isSemitermVec ℒₛₑₜ).pi.val) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_termBVGraph (M := M); have := wb_isUTermVec_neg_pi (M := M); have := wb_nthDef (M := M)
  simp only [isSemitermVec, HierarchySymbol.Semiformula.pi_mkDelta, HierarchySymbol.Semiformula.val_mkPi]
  wb_auto
  exact PRAWitnessTransfer.wb_exs_poly _ (by simp) ‘#3’
    (fun V _ _ e u h => ⟨u, by have h' := h; simp at h'; simp [h'.1], h⟩)
    (by
      wb_auto
      exact PRAWitnessTransfer.wb_exs_poly _ (by simp) ‘#0’
        (fun V _ _ e b h => ⟨b, by
          have h' := h; simp at h'; rw [h'.1]; exact termBV_le_self (e 0), h⟩) (by wb_auto))

end models
end DiophantineConsistency.PRAWitnessTermFunctions
