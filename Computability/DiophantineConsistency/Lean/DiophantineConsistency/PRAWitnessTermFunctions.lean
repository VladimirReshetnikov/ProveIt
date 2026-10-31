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
  PRAWitnessTermRec PRAWitnessRepeatVec PRAWitnessExpBounds

section sigma1
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem listMax_le_self (v : V) : listMax v ≤ v := listMaxss_le fun i _ => nth_le v i

theorem pair_le_sq {x y a b : V} (hx : x ≤ a) (hy : y ≤ b) : ⟪x, y⟫ ≤ (a + b + 1) * (a + b + 1) := by
  have h : x + y + 1 ≤ a + b + 1 := add_le_add (add_le_add hx hy) le_rfl
  exact le_trans (by simpa [sq] using pair_polybound x y) (mul_le_mul' h h)

theorem qqBvar_le (z : V) : ^#z ≤ (z + 1) * (z + 1) + 1 := by
  simpa [qqBvar] using add_le_add (pair_le_sq (le_refl (0 : V)) (le_refl z)) (le_refl 1)

theorem qqFvar_le (x : V) : ^&x ≤ (1 + x + 1) * (1 + x + 1) + 1 := by
  simpa [qqFvar] using add_le_add (pair_le_sq (le_refl (1 : V)) (le_refl x)) (le_refl 1)

theorem qqFunc_le (k f v : V) :
    ^func k f v ≤ (2 + ((k + ((f + v + 1) * (f + v + 1)) + 1) * (k + ((f + v + 1) * (f + v + 1)) + 1)) + 1) *
      (2 + ((k + ((f + v + 1) * (f + v + 1)) + 1) * (k + ((f + v + 1) * (f + v + 1)) + 1)) + 1) + 1 := by
  have h1 : ⟪f, v⟫ ≤ (f + v + 1) * (f + v + 1) := pair_le_sq le_rfl le_rfl
  have h2 := pair_le_sq (le_refl k) h1
  have h3 := pair_le_sq (le_refl (2 : V)) h2
  simpa [qqFunc] using add_le_add h3 (le_refl 1)

theorem le_sq_succ (x : V) : x ≤ (x + 1) * (x + 1) + 1 :=
  le_trans (le_of_lt (lt_add_one x))
    (le_trans (le_mul_of_one_le_right (by simp) (by simp)) le_self_add)

theorem sq_succ_mono {x y : V} (h : x ≤ y) : (x + 1) * (x + 1) + 1 ≤ (y + 1) * (y + 1) + 1 := by
  have h' : x + 1 ≤ y + 1 := add_le_add h le_rfl
  exact add_le_add (mul_le_mul' h' h') le_rfl

theorem termBShift_le (t : V) : termBShift ℒₛₑₜ t ≤ (t + 1) * (t + 1) + 1 := by
  by_cases ht : IsUTerm ℒₛₑₜ t
  · rcases IsUTerm.case ht with ⟨z, rfl⟩ | ⟨x, rfl⟩ | ⟨k, f, v, hkf, -, -⟩
    · rw [termBShift_bvar]
      have h2 : z + 1 ≤ ^#z := lt_iff_succ_le.mp (var_lt_qqBvar z)
      exact le_trans (qqBvar_le (z + 1)) (sq_succ_mono h2)
    · rw [termBShift_fvar]; exact le_sq_succ _
    · exact absurd hkf (not_isFunc k f)
  · simp [termBShift, Language.TermRec.Construction.result_prop_not _ _ _ ht]

theorem termBShiftVec_le (k w : V) :
    termBShiftVec ℒₛₑₜ k w ≤ repeatVec ((w + 1) * (w + 1) + 1) k := by
  by_cases hw : IsUTermVec ℒₛₑₜ k w
  · have hl := len_termBShiftVec hw
    have h := len_repeatVec_of_nth_le (v := termBShiftVec ℒₛₑₜ k w) (m := (w + 1) * (w + 1) + 1)
      (fun i hi => by
        rw [hl] at hi
        rw [nth_termBShiftVec hw hi]
        exact le_trans (termBShift_le _) (sq_succ_mono (nth_le w i)))
    rwa [hl] at h
  · simp [termBShiftVec, hw]

theorem sq2_mono {x y : V} (h : x ≤ y) : (x + 2) * (x + 2) + 1 ≤ (y + 2) * (y + 2) + 1 := by
  have h' : x + 2 ≤ y + 2 := add_le_add h le_rfl
  exact add_le_add (mul_le_mul' h' h') le_rfl

theorem le_sq2 (x : V) : x ≤ (x + 2) * (x + 2) + 1 :=
  le_trans (le_sq_succ x) (by
    have h' : x + 1 ≤ x + 2 := add_le_add le_rfl (by simp)
    exact add_le_add (mul_le_mul' h' h') le_rfl)

theorem termShift_le (t : V) : termShift ℒₛₑₜ t ≤ (t + 2) * (t + 2) + 1 := by
  by_cases ht : IsUTerm ℒₛₑₜ t
  · rcases IsUTerm.case ht with ⟨z, rfl⟩ | ⟨x, rfl⟩ | ⟨k, f, v, hkf, -, -⟩
    · rw [termShift_bvar]; exact le_sq2 _
    · rw [termShift_fvar]
      have h1 : x + 1 ≤ ^&x := lt_iff_succ_le.mp (var_lt_qqFvar x)
      have h2 : 1 + (x + 1) + 1 ≤ ^&x + 2 := by
        calc 1 + (x + 1) + 1 = (x + 1) + 2 := by rw [add_comm 1 (x + 1), add_assoc, one_add_one_eq_two]
          _ ≤ ^&x + 2 := add_le_add h1 le_rfl
      exact le_trans (qqFvar_le (x + 1)) (add_le_add (mul_le_mul' h2 h2) le_rfl)
    · exact absurd hkf (not_isFunc k f)
  · simp [termShift, Language.TermRec.Construction.result_prop_not _ _ _ ht]

theorem termShiftVec_le (k w : V) :
    termShiftVec ℒₛₑₜ k w ≤ repeatVec ((w + 2) * (w + 2) + 1) k := by
  by_cases hw : IsUTermVec ℒₛₑₜ k w
  · have hl := len_termShiftVec hw
    have h := len_repeatVec_of_nth_le (v := termShiftVec ℒₛₑₜ k w) (m := (w + 2) * (w + 2) + 1)
      (fun i hi => by
        rw [hl] at hi
        rw [nth_termShiftVec hw hi]
        exact le_trans (termShift_le _) (sq2_mono (nth_le w i)))
    rwa [hl] at h
  · simp [termShiftVec, hw]

theorem termSubst_le (w t : V) : termSubst ℒₛₑₜ w t ≤ t + w := by
  by_cases ht : IsUTerm ℒₛₑₜ t
  · rcases IsUTerm.case ht with ⟨z, rfl⟩ | ⟨x, rfl⟩ | ⟨k, f, v, hkf, -, -⟩
    · rw [termSubst_bvar]; exact le_trans (nth_le w z) le_add_self
    · rw [termSubst_fvar]; exact le_self_add
    · exact absurd hkf (not_isFunc k f)
  · simp [termSubst, Language.TermRec.Construction.result_prop_not _ _ _ ht]

theorem termSubstVec_le (k w v : V) : termSubstVec ℒₛₑₜ k w v ≤ repeatVec (v + w) k := by
  by_cases hv : IsUTermVec ℒₛₑₜ k v
  · have hl := len_termSubstVec (w := w) hv
    have h := len_repeatVec_of_nth_le (v := termSubstVec ℒₛₑₜ k w v) (m := v + w)
      (fun i hi => by
        rw [hl] at hi
        rw [nth_termSubstVec hv hi]
        exact le_trans (termSubst_le _ _) (add_le_add (nth_le v i) le_rfl))
    rwa [hl] at h
  · simp [termSubstVec, hv]

theorem repeatVec_mono_left {x x' : V} (h : x ≤ x') : ∀ k, repeatVec x k ≤ repeatVec x' k := by
  intro k
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih =>
    rw [repeatVec_succ, repeatVec_succ, adjoin_def, adjoin_def]
    exact add_le_add (pair_le_pair h ih) le_rfl

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

theorem wb_termBVVecGraph : WB M (termBVVecGraph ℒₛₑₜ).val :=
  wb_resultVec bvConstructions bv_clauses

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

/-! ### Substitution and shifts -/

/-- The polynomial bound of `qqFunc_le`, for argument positions `k f v`. -/
noncomputable def funcPoly {n : ℕ} (k f v : Fin n) : ArithmeticSemiterm Empty n :=
  ‘(2 + ((#k + ((#f + #v + 1) * (#f + #v + 1)) + 1) * (#k + ((#f + #v + 1) * (#f + #v + 1)) + 1)) + 1) *
    (2 + ((#k + ((#f + #v + 1) * (#f + #v + 1)) + 1) * (#k + ((#f + #v + 1) * (#f + #v + 1)) + 1)) + 1) + 1’

theorem subst_clauses : ClauseBounds TermSubst.blueprint M := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_nthDef (M := M); have := wb_qqFvarDef (M := M); have := wb_qqFuncDef (M := M)
  have hb : WB M TermSubst.blueprint.bvar.val := by
    simp only [TermSubst.blueprint, HierarchySymbol.Semiformula.val_mkSigma]; wb_auto
  have hf : WB M TermSubst.blueprint.fvar.val := by
    simp only [TermSubst.blueprint, HierarchySymbol.Semiformula.val_mkSigma]; wb_auto
  have hu : WB M TermSubst.blueprint.func.val := by
    simp only [TermSubst.blueprint, HierarchySymbol.Semiformula.val_mkSigma]; wb_auto
  refine ⟨hb, hf, hu, wb_neg_graphDelta_pi _ hb ‘#1’ ?_,
    wb_neg_graphDelta_pi _ hf ‘(1 + #0 + 1) * (1 + #0 + 1) + 1’ ?_,
    wb_neg_graphDelta_pi _ hu (funcPoly 0 1 3) ?_⟩
  · intro V _ _ e y h; simp [TermSubst.blueprint] at h; simp [h]
  · intro V _ _ e y h; simp [TermSubst.blueprint] at h; simpa [h] using qqFvar_le (e 0)
  · intro V _ _ e y h; simp [TermSubst.blueprint] at h; simpa [h, funcPoly] using qqFunc_le (e 0) (e 1) (e 3)

theorem shift_clauses : ClauseBounds TermShift.blueprint M := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_qqBvarDef (M := M); have := wb_qqFvarDef (M := M); have := wb_qqFuncDef (M := M)
  have hb : WB M TermShift.blueprint.bvar.val := by
    simp only [TermShift.blueprint, HierarchySymbol.Semiformula.val_mkSigma]; wb_auto
  have hf : WB M TermShift.blueprint.fvar.val := by
    simp only [TermShift.blueprint, HierarchySymbol.Semiformula.val_mkSigma]; wb_auto
  have hu : WB M TermShift.blueprint.func.val := by
    simp only [TermShift.blueprint, HierarchySymbol.Semiformula.val_mkSigma]; wb_auto
  refine ⟨hb, hf, hu, wb_neg_graphDelta_pi _ hb ‘(#0 + 1) * (#0 + 1) + 1’ ?_,
    wb_neg_graphDelta_pi _ hf ‘(1 + (#0 + 1) + 1) * (1 + (#0 + 1) + 1) + 1’ ?_,
    wb_neg_graphDelta_pi _ hu (funcPoly 0 1 3) ?_⟩
  · intro V _ _ e y h; simp [TermShift.blueprint] at h; simpa [h] using qqBvar_le (e 0)
  · intro V _ _ e y h; simp [TermShift.blueprint] at h; simpa [h] using qqFvar_le (e 0 + 1)
  · intro V _ _ e y h; simp [TermShift.blueprint] at h; simpa [h, funcPoly] using qqFunc_le (e 0) (e 1) (e 3)

theorem bShift_clauses : ClauseBounds TermBShift.blueprint M := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_qqBvarDef (M := M); have := wb_qqFvarDef (M := M); have := wb_qqFuncDef (M := M)
  have hb : WB M TermBShift.blueprint.bvar.val := by
    simp only [TermBShift.blueprint, HierarchySymbol.Semiformula.val_mkSigma]; wb_auto
  have hf : WB M TermBShift.blueprint.fvar.val := by
    simp only [TermBShift.blueprint, HierarchySymbol.Semiformula.val_mkSigma]; wb_auto
  have hu : WB M TermBShift.blueprint.func.val := by
    simp only [TermBShift.blueprint, HierarchySymbol.Semiformula.val_mkSigma]; wb_auto
  refine ⟨hb, hf, hu, wb_neg_graphDelta_pi _ hb ‘(#0 + 1 + 1) * (#0 + 1 + 1) + 1’ ?_,
    wb_neg_graphDelta_pi _ hf ‘(1 + #0 + 1) * (1 + #0 + 1) + 1’ ?_,
    wb_neg_graphDelta_pi _ hu (funcPoly 0 1 3) ?_⟩
  · intro V _ _ e y h; simp [TermBShift.blueprint] at h; simpa [h] using qqBvar_le (e 0 + 1)
  · intro V _ _ e y h; simp [TermBShift.blueprint] at h; simpa [h] using qqFvar_le (e 0)
  · intro V _ _ e y h; simp [TermBShift.blueprint] at h; simpa [h, funcPoly] using qqFunc_le (e 0) (e 1) (e 3)

noncomputable abbrev substConstructions : Constructions TermSubst.blueprint :=
  fun _ _ _ => TermSubst.construction
noncomputable abbrev shiftConstructions : Constructions TermShift.blueprint :=
  fun _ _ _ => TermShift.construction
noncomputable abbrev bShiftConstructions : Constructions TermBShift.blueprint :=
  fun _ _ _ => TermBShift.construction

theorem wb_termSubstGraph : WB M (termSubstGraph ℒₛₑₜ).val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  simp only [termSubstGraph, HierarchySymbol.Semiformula.val_rew]
  exact wb_rew _ (wb_result substConstructions subst_clauses)

theorem wb_termSubstVecGraph : WB M (termSubstVecGraph ℒₛₑₜ).val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  simp only [termSubstVecGraph, HierarchySymbol.Semiformula.val_rew]
  exact wb_rew _ (wb_resultVec substConstructions subst_clauses)

theorem wb_termShiftGraph : WB M (termShiftGraph ℒₛₑₜ).val :=
  wb_result shiftConstructions shift_clauses

theorem wb_termShiftVecGraph : WB M (termShiftVecGraph ℒₛₑₜ).val :=
  wb_resultVec shiftConstructions shift_clauses

theorem wb_termBShiftGraph : WB M (termBShiftGraph ℒₛₑₜ).val :=
  wb_result bShiftConstructions bShift_clauses

theorem wb_termBShiftVecGraph : WB M (termBShiftVecGraph ℒₛₑₜ).val :=
  wb_resultVec bShiftConstructions bShift_clauses

theorem wb_qVecGraph : WB M (qVecGraph ℒₛₑₜ).val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_lenDef (M := M); have := wb_termBShiftVecGraph (M := M); have := wb_qqBvarDef (M := M)
  have := wb_adjoinDef (M := M)
  simp only [qVecGraph, HierarchySymbol.Semiformula.val_mkSigma]
  refine PRAWitnessTransfer.wb_exs_poly _ (by simp) ‘#1’
    (fun V _ _ e u h => ⟨u, by have h' := h; simp at h'; simp [h'.1], h⟩) ?_
  wb_auto
  refine PRAWitnessTransfer.wb_exs_bound _ (by simp)
    (expGraph2 ‘(#2 + 1) * (#2 + 1) + 1 + 2’ ‘2 * #0’) (expBound2 ‘(#2 + 1) * (#2 + 1) + 1 + 2’ ‘2 * #0’)
    (dominates_expBound2 _ _) (mono_expBound2 _ _) ?_ ?_
  · intro V _ _ e x h
    have h' := h; simp at h'
    refine ⟨Exp.exp (((e 2 + 1) * (e 2 + 1) + 1 + 2) * Exp.exp (2 * e 0)), ?_, x, ?_, h⟩
    · rw [eval_expGraph2]
      exact ⟨Exp.exp (2 * e 0), by simpa using exponential_exp (2 * e 0),
        by simpa using exponential_exp (((e 2 + 1) * (e 2 + 1) + 1 + 2) * Exp.exp (2 * e 0))⟩
    · rw [h'.1]
      exact le_trans (termBShiftVec_le _ _) (le_of_lt (repeatVec_lt _ _))
  · wb_auto
    exact PRAWitnessTransfer.wb_exs_poly _ (by simp) ‘1’
      (fun V _ _ e u h => ⟨u, by have h' := h; simp at h'; simp [h'.1, qqBvar, pair], h⟩) (by wb_auto)

end models
end DiophantineConsistency.PRAWitnessTermFunctions
