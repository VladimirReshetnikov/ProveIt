import DiophantineConsistency.PRAWitnessFormulaRec
/-! # Witness bounds for the formula functions over `ℒₛₑₜ`

Each `UformulaRec1` instance supplies `PRAWitnessFormulaRec.ClauseBounds`
(its clauses are `𝚺₀`-shaped code constructions whose values are bounded by
polynomials in their arguments, `code2_le`–`code4_le`) and
`PRAWitnessFormulaRec.RecShape` (no parameter growth, children below the
result). -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAWitnessFormulaFunctions
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open StrictSigmaOneInduction PRAWitnessCalculus PRAWitnessArithmetic PRAWitnessVectors PRAWitnessSetTerms
  PRAWitnessTermRec PRAWitnessTermFunctions PRAWitnessFormulas PRAWitnessFormulaRec PRAWitnessRepeatVec
  PRAWitnessExpBounds

section sigma1
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem code2_le (c a : V) : ⟪c, a⟫ + 1 ≤ (c + a + 1) * (c + a + 1) + 1 :=
  add_le_add (pair_le_sq le_rfl le_rfl) le_rfl

theorem code3_le (c a b : V) :
    ⟪c, a, b⟫ + 1 ≤ (c + (a + b + 1) * (a + b + 1) + 1) * (c + (a + b + 1) * (a + b + 1) + 1) + 1 :=
  add_le_add (pair_le_sq le_rfl (pair_le_sq le_rfl le_rfl)) le_rfl

theorem code4_le (c a b d : V) :
    ⟪c, a, b, d⟫ + 1 ≤
      (c + (a + (b + d + 1) * (b + d + 1) + 1) * (a + (b + d + 1) * (b + d + 1) + 1) + 1) *
        (c + (a + (b + d + 1) * (b + d + 1) + 1) * (a + (b + d + 1) * (b + d + 1) + 1) + 1) + 1 :=
  add_le_add (pair_le_sq le_rfl (pair_le_sq le_rfl (pair_le_sq le_rfl le_rfl))) le_rfl

theorem code4_le_repeatVec {c k R v' m j : V} (hc : c ≤ m) (hk : k ≤ m) (hR : R ≤ m)
    (hv : v' ≤ repeatVec m j) : ⟪c, k, R, v'⟫ + 1 ≤ repeatVec m (j + 1 + 1 + 1) := by
  simp only [repeatVec_succ, adjoin_def]
  exact add_le_add (pair_le_pair hc (le_trans (pair_le_pair hk
    (le_trans (pair_le_pair hR hv) le_self_add)) le_self_add)) le_rfl

theorem termBVVec_le (k v : V) : termBVVec ℒₛₑₜ k v ≤ repeatVec v k := by
  by_cases hv : IsUTermVec ℒₛₑₜ k v
  · have hl := len_termBVVec hv
    have h := len_repeatVec_of_nth_le (v := termBVVec ℒₛₑₜ k v) (m := v)
      (fun i hi => by
        rw [hl] at hi
        rw [nth_termBVVec hv hi]
        exact le_trans (termBV_le_self _) (nth_le v i))
    rwa [hl] at h
  · simp [termBVVec, hv]

theorem listMax_termBVVec_le (k v : V) : listMax (termBVVec ℒₛₑₜ k v) ≤ v := by
  by_cases hv : IsUTermVec ℒₛₑₜ k v
  · refine listMaxss_le fun i hi => ?_
    rw [len_termBVVec hv] at hi
    rw [nth_termBVVec hv hi]
    exact le_trans (termBV_le_self _) (nth_le v i)
  · simp [termBVVec, hv]

/-- Over `ℒₛₑₜ` the bound-variable bound of a formula code is at most the code. -/
theorem bv_le_self (p : V) : bv ℒₛₑₜ p ≤ p := by
  by_cases hp : IsUFormula ℒₛₑₜ p
  · refine IsUFormula.ISigma1.sigma1_succ_induction (P := fun p => bv ℒₛₑₜ p ≤ p) (by definability)
      ?_ ?_ (by simp) (by simp) ?_ ?_ ?_ ?_ p hp
    · intro k r v hr hv
      rw [bv_rel hr hv]; exact le_trans (listMax_termBVVec_le k v) (le_of_lt (v_lt_rel k r v))
    · intro k r v hr hv
      rw [bv_nrel hr hv]; exact le_trans (listMax_termBVVec_le k v) (le_of_lt (v_lt_nrel k r v))
    · intro p q hp hq ihp ihq
      rw [bv_and hp hq]
      exact max_le (le_trans ihp (le_of_lt (lt_K!_left p q))) (le_trans ihq (le_of_lt (lt_K!_right p q)))
    · intro p q hp hq ihp ihq
      rw [bv_or hp hq]
      exact max_le (le_trans ihp (le_of_lt (lt_or_left p q))) (le_trans ihq (le_of_lt (lt_or_right p q)))
    · intro p hp ih
      rw [bv_all hp]; exact le_trans tsub_le_self (le_trans ih (le_of_lt (lt_forall p)))
    · intro p hp ih
      rw [bv_ex hp]; exact le_trans tsub_le_self (le_trans ih (le_of_lt (lt_exists p)))
  · rw [bv_eq_of_not_isUFormula hp]; simp

theorem le_succ_of_lt {a b : V} (h : a < b) : a ≤ b + 1 := le_trans (le_of_lt h) le_self_add

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

theorem neg_clauses : PRAWitnessFormulaRec.ClauseBounds Negation.blueprint M := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_qqRelDef (M := M); have := wb_qqNRelDef (M := M); have := wb_qqVerumDef (M := M)
  have := wb_qqFalsumDef (M := M); have := wb_qqAndDef (M := M); have := wb_qqOrDef (M := M)
  have := wb_qqAllDef (M := M); have := wb_qqExsDef (M := M)
  have h_rel : WB M Negation.blueprint.rel.val := by
    simp only [Negation.blueprint, HierarchySymbol.Semiformula.val_mkSigma]; wb_auto
  have h_nrel : WB M Negation.blueprint.nrel.val := by
    simp only [Negation.blueprint, HierarchySymbol.Semiformula.val_mkSigma]; wb_auto
  have h_verum : WB M Negation.blueprint.verum.val := by
    simp only [Negation.blueprint, HierarchySymbol.Semiformula.val_mkSigma]; wb_auto
  have h_falsum : WB M Negation.blueprint.falsum.val := by
    simp only [Negation.blueprint, HierarchySymbol.Semiformula.val_mkSigma]; wb_auto
  have h_and : WB M Negation.blueprint.and.val := by
    simp only [Negation.blueprint, HierarchySymbol.Semiformula.val_mkSigma]; wb_auto
  have h_or : WB M Negation.blueprint.or.val := by
    simp only [Negation.blueprint, HierarchySymbol.Semiformula.val_mkSigma]; wb_auto
  have h_all : WB M Negation.blueprint.all.val := by
    simp only [Negation.blueprint, HierarchySymbol.Semiformula.val_mkSigma]; wb_auto
  have h_exs : WB M Negation.blueprint.exs.val := by
    simp only [Negation.blueprint, HierarchySymbol.Semiformula.val_mkSigma]; wb_auto
  have h_allChanges : WB M Negation.blueprint.allChanges.val := by
    simp only [Negation.blueprint, HierarchySymbol.Semiformula.val_mkSigma]; wb_auto
  have h_exsChanges : WB M Negation.blueprint.exsChanges.val := by
    simp only [Negation.blueprint, HierarchySymbol.Semiformula.val_mkSigma]; wb_auto
  refine ⟨h_rel, h_nrel, h_verum, h_falsum, h_and, h_or, h_all, h_exs, h_allChanges, h_exsChanges,
    wb_neg_graphDelta_pi _ h_rel ‘(1 + (#1 + (#2 + #3 + 1) * (#2 + #3 + 1) + 1) * (#1 + (#2 + #3 + 1) * (#2 + #3 + 1) + 1) + 1) * (1 + (#1 + (#2 + #3 + 1) * (#2 + #3 + 1) + 1) * (#1 + (#2 + #3 + 1) * (#2 + #3 + 1) + 1) + 1) + 1’ ?_,
    wb_neg_graphDelta_pi _ h_nrel ‘(0 + (#1 + (#2 + #3 + 1) * (#2 + #3 + 1) + 1) * (#1 + (#2 + #3 + 1) * (#2 + #3 + 1) + 1) + 1) * (0 + (#1 + (#2 + #3 + 1) * (#2 + #3 + 1) + 1) * (#1 + (#2 + #3 + 1) * (#2 + #3 + 1) + 1) + 1) + 1’ ?_,
    wb_neg_graphDelta_pi _ h_verum ‘(3 + 0 + 1) * (3 + 0 + 1) + 1’ ?_,
    wb_neg_graphDelta_pi _ h_falsum ‘(2 + 0 + 1) * (2 + 0 + 1) + 1’ ?_,
    wb_neg_graphDelta_pi _ h_and ‘(5 + (#3 + #4 + 1) * (#3 + #4 + 1) + 1) * (5 + (#3 + #4 + 1) * (#3 + #4 + 1) + 1) + 1’ ?_,
    wb_neg_graphDelta_pi _ h_or ‘(4 + (#3 + #4 + 1) * (#3 + #4 + 1) + 1) * (4 + (#3 + #4 + 1) * (#3 + #4 + 1) + 1) + 1’ ?_,
    wb_neg_graphDelta_pi _ h_all ‘(7 + #2 + 1) * (7 + #2 + 1) + 1’ ?_,
    wb_neg_graphDelta_pi _ h_exs ‘(6 + #2 + 1) * (6 + #2 + 1) + 1’ ?_,
    ?_, ?_⟩
  · intro V _ _ e y h; simp [Negation.blueprint] at h; rw [h]; simpa [qqNRel, numeral_eq_natCast] using code4_le 1 (e 1) (e 2) (e 3)
  · intro V _ _ e y h; simp [Negation.blueprint] at h; rw [h]; simpa [qqRel, numeral_eq_natCast] using code4_le 0 (e 1) (e 2) (e 3)
  · intro V _ _ e y h; simp [Negation.blueprint] at h; rw [h]; simpa [qqFalsum, numeral_eq_natCast] using code2_le (3 : V) 0
  · intro V _ _ e y h; simp [Negation.blueprint] at h; rw [h]; simpa [qqVerum, numeral_eq_natCast] using code2_le (2 : V) 0
  · intro V _ _ e y h; simp [Negation.blueprint] at h; rw [h]; simpa [qqOr, numeral_eq_natCast] using code3_le 5 (e 3) (e 4)
  · intro V _ _ e y h; simp [Negation.blueprint] at h; rw [h]; simpa [qqAnd, numeral_eq_natCast] using code3_le 4 (e 3) (e 4)
  · intro V _ _ e y h; simp [Negation.blueprint] at h; rw [h]; simpa [qqExs, numeral_eq_natCast] using code2_le 7 (e 2)
  · intro V _ _ e y h; simp [Negation.blueprint] at h; rw [h]; simpa [qqAll, numeral_eq_natCast] using code2_le 6 (e 2)
  · intro V _ _ a b h; simp [Negation.blueprint] at h; simp [h]
  · intro V _ _ a b h; simp [Negation.blueprint] at h; simp [h]

noncomputable abbrev negConstructions : PRAWitnessFormulaRec.Constructions Negation.blueprint :=
  fun _ _ _ => Negation.construction

theorem neg_shape (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :
    PRAWitnessFormulaRec.RecShape (negConstructions V) where
  all_le _ := by simp [Negation.construction]
  exs_le _ := by simp [Negation.construction]
  and_le _ _ _ y₁ y₂ := ⟨le_succ_of_lt (lt_or_left y₁ y₂), le_succ_of_lt (lt_or_right y₁ y₂)⟩
  or_le _ _ _ y₁ y₂ := ⟨le_succ_of_lt (lt_K!_left y₁ y₂), le_succ_of_lt (lt_K!_right y₁ y₂)⟩
  all_y _ _ y₁ := le_succ_of_lt (lt_exists y₁)
  exs_y _ _ y₁ := le_succ_of_lt (lt_forall y₁)

theorem wb_negGraph : WB M (negGraph ℒₛₑₜ).val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  simp only [negGraph, HierarchySymbol.Semiformula.val_rew]
  exact wb_rew _ (PRAWitnessFormulaRec.wb_result negConstructions neg_shape neg_clauses)

theorem shift_clauses : PRAWitnessFormulaRec.ClauseBounds (Shift.blueprint ℒₛₑₜ) M := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_qqRelDef (M := M); have := wb_qqNRelDef (M := M); have := wb_qqVerumDef (M := M)
  have := wb_qqFalsumDef (M := M); have := wb_qqAndDef (M := M); have := wb_qqOrDef (M := M)
  have := wb_qqAllDef (M := M); have := wb_qqExsDef (M := M)
  have := wb_termShiftVecGraph (M := M)
  have h_rel : WB M (Shift.blueprint ℒₛₑₜ).rel.val := by
    simp only [Shift.blueprint, HierarchySymbol.Semiformula.val_mkSigma]
    exact PRAWitnessTransfer.wb_exs_poly _ (by simp) ‘#0’
      (fun V _ _ e u h => ⟨u, by
        have h' := h; simp at h'
        simpa [h'.2] using le_of_lt (v_lt_rel (e 2) (e 3) u), h⟩) (by wb_auto)
  have h_nrel : WB M (Shift.blueprint ℒₛₑₜ).nrel.val := by
    simp only [Shift.blueprint, HierarchySymbol.Semiformula.val_mkSigma]
    exact PRAWitnessTransfer.wb_exs_poly _ (by simp) ‘#0’
      (fun V _ _ e u h => ⟨u, by
        have h' := h; simp at h'
        simpa [h'.2] using le_of_lt (v_lt_nrel (e 2) (e 3) u), h⟩) (by wb_auto)
  have h_verum : WB M (Shift.blueprint ℒₛₑₜ).verum.val := by
    simp only [Shift.blueprint, HierarchySymbol.Semiformula.val_mkSigma]; wb_auto
  have h_falsum : WB M (Shift.blueprint ℒₛₑₜ).falsum.val := by
    simp only [Shift.blueprint, HierarchySymbol.Semiformula.val_mkSigma]; wb_auto
  have h_and : WB M (Shift.blueprint ℒₛₑₜ).and.val := by
    simp only [Shift.blueprint, HierarchySymbol.Semiformula.val_mkSigma]; wb_auto
  have h_or : WB M (Shift.blueprint ℒₛₑₜ).or.val := by
    simp only [Shift.blueprint, HierarchySymbol.Semiformula.val_mkSigma]; wb_auto
  have h_all : WB M (Shift.blueprint ℒₛₑₜ).all.val := by
    simp only [Shift.blueprint, HierarchySymbol.Semiformula.val_mkSigma]; wb_auto
  have h_exs : WB M (Shift.blueprint ℒₛₑₜ).exs.val := by
    simp only [Shift.blueprint, HierarchySymbol.Semiformula.val_mkSigma]; wb_auto
  have h_allChanges : WB M (Shift.blueprint ℒₛₑₜ).allChanges.val := by
    simp only [Shift.blueprint, HierarchySymbol.Semiformula.val_mkSigma]; wb_auto
  have h_exsChanges : WB M (Shift.blueprint ℒₛₑₜ).exsChanges.val := by
    simp only [Shift.blueprint, HierarchySymbol.Semiformula.val_mkSigma]; wb_auto
  refine ⟨h_rel, h_nrel, h_verum, h_falsum, h_and, h_or, h_all, h_exs, h_allChanges, h_exsChanges,
    wb_neg_graphDelta_pi_exp _ h_rel ‘(#3 + 2) * (#3 + 2) + 1 + #1 + #2 + 2’ ‘2 * (#1 + 1 + 1 + 1)’ ?_,
    wb_neg_graphDelta_pi_exp _ h_nrel ‘(#3 + 2) * (#3 + 2) + 1 + #1 + #2 + 2’ ‘2 * (#1 + 1 + 1 + 1)’ ?_,
    wb_neg_graphDelta_pi _ h_verum ‘(2 + 0 + 1) * (2 + 0 + 1) + 1’ ?_,
    wb_neg_graphDelta_pi _ h_falsum ‘(3 + 0 + 1) * (3 + 0 + 1) + 1’ ?_,
    wb_neg_graphDelta_pi _ h_and ‘(4 + (#3 + #4 + 1) * (#3 + #4 + 1) + 1) * (4 + (#3 + #4 + 1) * (#3 + #4 + 1) + 1) + 1’ ?_,
    wb_neg_graphDelta_pi _ h_or ‘(5 + (#3 + #4 + 1) * (#3 + #4 + 1) + 1) * (5 + (#3 + #4 + 1) * (#3 + #4 + 1) + 1) + 1’ ?_,
    wb_neg_graphDelta_pi _ h_all ‘(6 + #2 + 1) * (6 + #2 + 1) + 1’ ?_,
    wb_neg_graphDelta_pi _ h_exs ‘(7 + #2 + 1) * (7 + #2 + 1) + 1’ ?_,
    ?_, ?_⟩
  · intro V _ _ e y h
    simp [Shift.blueprint] at h
    rw [h]
    have hm : (e 3 + 2) * (e 3 + 2) + 1 ≤ (e 3 + 2) * (e 3 + 2) + 1 + e 1 + e 2 := le_trans le_self_add le_self_add
    have hv := le_trans (termShiftVec_le (e 1) (e 3)) (repeatVec_mono_left hm (e 1))
    have hy := code4_le_repeatVec (c := 0) (by simp) (le_trans le_add_self le_self_add) le_add_self hv
    have := le_trans hy (le_of_lt (repeatVec_lt _ _))
    simpa [qqRel, numeral_eq_natCast] using this
  · intro V _ _ e y h
    simp [Shift.blueprint] at h
    rw [h]
    have hm : (e 3 + 2) * (e 3 + 2) + 1 ≤ (e 3 + 2) * (e 3 + 2) + 1 + e 1 + e 2 := le_trans le_self_add le_self_add
    have hv := le_trans (termShiftVec_le (e 1) (e 3)) (repeatVec_mono_left hm (e 1))
    have hy := code4_le_repeatVec (c := 1)
      (le_trans (le_trans le_add_self le_self_add) le_self_add) (le_trans le_add_self le_self_add) le_add_self hv
    have := le_trans hy (le_of_lt (repeatVec_lt _ _))
    simpa [qqNRel, numeral_eq_natCast] using this
  · intro V _ _ e y h; simp [Shift.blueprint] at h; rw [h]; simpa [qqVerum, numeral_eq_natCast] using code2_le (2 : V) 0
  · intro V _ _ e y h; simp [Shift.blueprint] at h; rw [h]; simpa [qqFalsum, numeral_eq_natCast] using code2_le (3 : V) 0
  · intro V _ _ e y h; simp [Shift.blueprint] at h; rw [h]; simpa [qqAnd, numeral_eq_natCast] using code3_le 4 (e 3) (e 4)
  · intro V _ _ e y h; simp [Shift.blueprint] at h; rw [h]; simpa [qqOr, numeral_eq_natCast] using code3_le 5 (e 3) (e 4)
  · intro V _ _ e y h; simp [Shift.blueprint] at h; rw [h]; simpa [qqAll, numeral_eq_natCast] using code2_le 6 (e 2)
  · intro V _ _ e y h; simp [Shift.blueprint] at h; rw [h]; simpa [qqExs, numeral_eq_natCast] using code2_le 7 (e 2)
  · intro V _ _ a b h; simp [Shift.blueprint] at h; simp [h]
  · intro V _ _ a b h; simp [Shift.blueprint] at h; simp [h]

noncomputable abbrev shiftConstructions : PRAWitnessFormulaRec.Constructions (Shift.blueprint ℒₛₑₜ) :=
  fun _ _ _ => Shift.construction ℒₛₑₜ

theorem shift_shape (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :
    PRAWitnessFormulaRec.RecShape (shiftConstructions V) where
  all_le _ := by simp [Shift.construction]
  exs_le _ := by simp [Shift.construction]
  and_le _ _ _ y₁ y₂ := ⟨le_succ_of_lt (lt_K!_left y₁ y₂), le_succ_of_lt (lt_K!_right y₁ y₂)⟩
  or_le _ _ _ y₁ y₂ := ⟨le_succ_of_lt (lt_or_left y₁ y₂), le_succ_of_lt (lt_or_right y₁ y₂)⟩
  all_y _ _ y₁ := le_succ_of_lt (lt_forall y₁)
  exs_y _ _ y₁ := le_succ_of_lt (lt_exists y₁)

theorem wb_shiftGraph : WB M (shiftGraph ℒₛₑₜ).val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  simp only [shiftGraph, HierarchySymbol.Semiformula.val_rew]
  exact wb_rew _ (PRAWitnessFormulaRec.wb_result shiftConstructions shift_shape shift_clauses)

theorem bv_clauses : PRAWitnessFormulaRec.ClauseBounds (BV.blueprint ℒₛₑₜ) M := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_termBVVecGraph (M := M); have := wb_listMaxDef (M := M); have := wb_maxDef (M := M)
  have := wb_subDef (M := M)
  have h_rel : WB M (BV.blueprint ℒₛₑₜ).rel.val := by
    simp only [BV.blueprint, HierarchySymbol.Semiformula.val_mkSigma]
    refine PRAWitnessTransfer.wb_exs_bound _ (by simp)
      (expGraph2 ‘#4 + 2’ ‘2 * #2’) (expBound2 ‘#4 + 2’ ‘2 * #2’)
      (dominates_expBound2 _ _) (mono_expBound2 _ _) (fun V _ _ e x h => ?_) (by wb_auto)
    have h' := h; simp at h'
    refine ⟨Exp.exp ((e 4 + 2) * Exp.exp (2 * e 2)), ?_, x, ?_, h⟩
    · rw [eval_expGraph2]
      exact ⟨Exp.exp (2 * e 2), by simpa using exponential_exp (2 * e 2),
        by simpa using exponential_exp ((e 4 + 2) * Exp.exp (2 * e 2))⟩
    · rw [h'.1]; exact le_trans (termBVVec_le _ _) (le_of_lt (repeatVec_lt _ _))
  have h_nrel : WB M (BV.blueprint ℒₛₑₜ).nrel.val := by
    simp only [BV.blueprint, HierarchySymbol.Semiformula.val_mkSigma]
    refine PRAWitnessTransfer.wb_exs_bound _ (by simp)
      (expGraph2 ‘#4 + 2’ ‘2 * #2’) (expBound2 ‘#4 + 2’ ‘2 * #2’)
      (dominates_expBound2 _ _) (mono_expBound2 _ _) (fun V _ _ e x h => ?_) (by wb_auto)
    have h' := h; simp at h'
    refine ⟨Exp.exp ((e 4 + 2) * Exp.exp (2 * e 2)), ?_, x, ?_, h⟩
    · rw [eval_expGraph2]
      exact ⟨Exp.exp (2 * e 2), by simpa using exponential_exp (2 * e 2),
        by simpa using exponential_exp ((e 4 + 2) * Exp.exp (2 * e 2))⟩
    · rw [h'.1]; exact le_trans (termBVVec_le _ _) (le_of_lt (repeatVec_lt _ _))
  have h_verum : WB M (BV.blueprint ℒₛₑₜ).verum.val := by
    simp only [BV.blueprint, HierarchySymbol.Semiformula.val_mkSigma]; wb_auto
  have h_falsum : WB M (BV.blueprint ℒₛₑₜ).falsum.val := by
    simp only [BV.blueprint, HierarchySymbol.Semiformula.val_mkSigma]; wb_auto
  have h_and : WB M (BV.blueprint ℒₛₑₜ).and.val := by
    simp only [BV.blueprint, HierarchySymbol.Semiformula.val_mkSigma]; wb_auto
  have h_or : WB M (BV.blueprint ℒₛₑₜ).or.val := by
    simp only [BV.blueprint, HierarchySymbol.Semiformula.val_mkSigma]; wb_auto
  have h_all : WB M (BV.blueprint ℒₛₑₜ).all.val := by
    simp only [BV.blueprint, HierarchySymbol.Semiformula.val_mkSigma]; wb_auto
  have h_exs : WB M (BV.blueprint ℒₛₑₜ).exs.val := by
    simp only [BV.blueprint, HierarchySymbol.Semiformula.val_mkSigma]; wb_auto
  have h_allChanges : WB M (BV.blueprint ℒₛₑₜ).allChanges.val := by
    simp only [BV.blueprint, HierarchySymbol.Semiformula.val_mkSigma]; wb_auto
  have h_exsChanges : WB M (BV.blueprint ℒₛₑₜ).exsChanges.val := by
    simp only [BV.blueprint, HierarchySymbol.Semiformula.val_mkSigma]; wb_auto
  refine ⟨h_rel, h_nrel, h_verum, h_falsum, h_and, h_or, h_all, h_exs, h_allChanges, h_exsChanges,
    wb_neg_graphDelta_pi _ h_rel ‘#3’ ?_, wb_neg_graphDelta_pi _ h_nrel ‘#3’ ?_,
    wb_neg_graphDelta_pi _ h_verum ‘0’ ?_, wb_neg_graphDelta_pi _ h_falsum ‘0’ ?_,
    wb_neg_graphDelta_pi _ h_and ‘#3 + #4’ ?_, wb_neg_graphDelta_pi _ h_or ‘#3 + #4’ ?_,
    wb_neg_graphDelta_pi _ h_all ‘#2’ ?_, wb_neg_graphDelta_pi _ h_exs ‘#2’ ?_, ?_, ?_⟩
  · intro V _ _ e y h; simp [BV.blueprint] at h; rw [h]; simpa using listMax_termBVVec_le (e 1) (e 3)
  · intro V _ _ e y h; simp [BV.blueprint] at h; rw [h]; simpa using listMax_termBVVec_le (e 1) (e 3)
  · intro V _ _ e y h; simp [BV.blueprint] at h; simp [h]
  · intro V _ _ e y h; simp [BV.blueprint] at h; simp [h]
  · intro V _ _ e y h; simp [BV.blueprint] at h; rw [h]; simp
  · intro V _ _ e y h; simp [BV.blueprint] at h; rw [h]; simp
  · intro V _ _ e y h; simp [BV.blueprint] at h; rw [h]; simp
  · intro V _ _ e y h; simp [BV.blueprint] at h; rw [h]; simp
  · intro V _ _ a b h; simp [BV.blueprint] at h; simp [h]
  · intro V _ _ a b h; simp [BV.blueprint] at h; simp [h]

noncomputable abbrev bvConstructions : PRAWitnessFormulaRec.Constructions (BV.blueprint ℒₛₑₜ) :=
  fun _ _ _ => BV.construction ℒₛₑₜ

theorem bv_shape (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :
    PRAWitnessFormulaRec.RecShape (bvConstructions V) where
  all_le _ := by simp [BV.construction]
  exs_le _ := by simp [BV.construction]
  and_le _ _ _ y₁ y₂ := by
    simp only [BV.construction]
    exact ⟨le_trans (le_max_left y₁ y₂) le_self_add, le_trans (le_max_right y₁ y₂) le_self_add⟩
  or_le _ _ _ y₁ y₂ := by
    simp only [BV.construction]
    exact ⟨le_trans (le_max_left y₁ y₂) le_self_add, le_trans (le_max_right y₁ y₂) le_self_add⟩
  all_y _ _ y₁ := by simp only [BV.construction]; exact le_tsub_add
  exs_y _ _ y₁ := by simp only [BV.construction]; exact le_tsub_add

theorem wb_bvGraph : WB M (bvGraph ℒₛₑₜ).val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  simp only [bvGraph, HierarchySymbol.Semiformula.val_rew]
  exact wb_rew _ (PRAWitnessFormulaRec.wb_result bvConstructions bv_shape bv_clauses)

theorem wb_isSemiformula_sigma : WB M (isSemiformula ℒₛₑₜ).sigma.val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_bvGraph (M := M); have := wb_isUFormula_sigma (M := M)
  simp only [isSemiformula, HierarchySymbol.Semiformula.sigma_mkDelta, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto
  exact wb_exs_term ‘#0’ (fun e y h => by simp at h; exact h.2) (by wb_auto)

theorem wb_isSemiformula_neg_pi : WB M (∼(isSemiformula ℒₛₑₜ).pi.val) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_bvGraph (M := M); have := wb_isUFormula_neg_pi (M := M)
  simp only [isSemiformula, HierarchySymbol.Semiformula.pi_mkDelta, HierarchySymbol.Semiformula.val_mkPi]
  wb_auto
  exact PRAWitnessTransfer.wb_exs_poly _ (by simp) ‘#1’
    (fun V _ _ e b h => ⟨b, by
      have h' := h; simp at h'; rw [h'.1]; exact bv_le_self (e 1), h⟩) (by wb_auto)

end models
end DiophantineConsistency.PRAWitnessFormulaFunctions
