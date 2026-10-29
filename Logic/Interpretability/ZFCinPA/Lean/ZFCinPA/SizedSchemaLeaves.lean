import ZFCinPA.SizedPlaceholderCongruence
import ZFCinPA.SizedTemplateAxioms
import ZFCinPA.OpenTemplateClosure
import ZFCinPA.ModelCodedSchemaAxioms
import ZFCinPA.ModelCodedRenamingAxioms
import ZFCinPA.OpenSchemaTemplates

/-!
# Bounded separation and replacement leaves

The remaining template axiom leaves are the translated schema instances
`translateFormula Ks (emb (sepBodySource p).univCl)` and their replacement
analogues. `OpenSchemaTemplates` proves them through `closeTemplate`, whose
`generalizeAll` picks its codes with `Classical.choose`.

For shift-fixed placeholders (the convention of `SetPlaceholders`), the
translated sentence is `∀^N T` with `T` shift-fixed, and `∀^m T` with
`m = bv T ≤ N` is *literally* a recognized `𝗭𝗙` axiom (`SchemaRecognizer`):
its opening at `&0 … &(m-1)` is the schema body of the translated matrix
(`subst_congr` moves the opening from `N` to `m` variables). The leaf is
therefore one `axm` rule followed by `N - m` vacuous generalizations
(`vac_gen`), and its level is that of the sentence plus `2N + 5`.
-/
set_option autoImplicit false
noncomputable section

namespace LeanProofs.ZFCinPA.SizedSchemaLeaves

open LO LO.FirstOrder LO.FirstOrder.SetTheory LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic
open LeanProofs.ZFCinPA
open LeanProofs.BoundedPAConsistency.SizedDerivation
open LeanProofs.ZFCinPA.SetCodeLevels LeanProofs.ZFCinPA.LevelDerivation
open LeanProofs.ZFCinPA.SizedCongruence LeanProofs.ZFCinPA.SetPlaceholders
open LeanProofs.ZFCinPA.OpenSetTemplateCompiler LeanProofs.ZFCinPA.OpenTemplateClosure
open LeanProofs.ZFCinPA.TemplateTranslateLevel LeanProofs.ZFCinPA.SizedTemplateAxioms
open LeanProofs.ZFCinPA.SizedPlaceholderCongruence (lt_lvB_of)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Substitution facts -/

theorem subst_closed {p n m w : V} (hp : IsSemiformula ℒₛₑₜ 0 p) (hw : IsSemitermVec ℒₛₑₜ n m w) :
    subst ℒₛₑₜ w p = p := by
  have h0 : subst ℒₛₑₜ (0 : V) p = p := Bootstrapping.subst_eq_self hp (by simp) (by simp)
  have hv : IsSemitermVec ℒₛₑₜ 0 n (0 : V) := by simp
  calc subst ℒₛₑₜ w p = subst ℒₛₑₜ w (subst ℒₛₑₜ 0 p) := by rw [h0]
    _ = subst ℒₛₑₜ (termSubstVec ℒₛₑₜ 0 w 0) p := Bootstrapping.substs_substs hp hw hv
    _ = subst ℒₛₑₜ 0 p := by
        congr 1
        apply nth_ext' 0 (by simp [len_termSubstVec hv.isUTerm]) (by simp)
        intro i hi; simp at hi
    _ = p := h0

theorem free_closed {p : V} (hp : IsSemiformula ℒₛₑₜ 0 p) (hs : shift ℒₛₑₜ p = p) :
    free ℒₛₑₜ p = p := by
  unfold free substs1
  rw [hs]
  exact subst_closed hp (by simp : IsSemitermVec ℒₛₑₜ 1 0 (^&0 ∷ 0 : V))

set_option maxHeartbeats 1000000 in
/-- Substitution only reads the entries below the bound-variable count. -/
theorem subst_congr {n p : V} (hp : IsSemiformula ℒₛₑₜ n p) :
    ∀ l M w l' M' w' : V, IsSemitermVec ℒₛₑₜ l M w → IsSemitermVec ℒₛₑₜ l' M' w' → n ≤ l → n ≤ l' →
      (∀ i < n, w.[i] = w'.[i]) → subst ℒₛₑₜ w p = subst ℒₛₑₜ w' p := by
  apply IsSemiformula.pi1_structural_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  · intro n k R v hR hv l M w l' M' w' hw hw' hl hl' H
    simp only [substs_rel hR hv.isUTerm, qqRel_inj, true_and]
    apply nth_ext' k (by simp [hv.isUTerm]) (by simp [hv.isUTerm])
    intro i hi
    rw [nth_termSubstVec hv.isUTerm hi, nth_termSubstVec hv.isUTerm hi]
    rcases term_var (hv.nth hi).isUTerm with ⟨z, hz⟩ | ⟨x, hx⟩
    · have hzn : z < n := by simpa [hz] using hv.nth hi
      rw [hz, termSubst_bvar, termSubst_bvar, H z hzn]
    · rw [hx, termSubst_fvar, termSubst_fvar]
  · intro n k R v hR hv l M w l' M' w' hw hw' hl hl' H
    simp only [substs_nrel hR hv.isUTerm, qqNRel_inj, true_and]
    apply nth_ext' k (by simp [hv.isUTerm]) (by simp [hv.isUTerm])
    intro i hi
    rw [nth_termSubstVec hv.isUTerm hi, nth_termSubstVec hv.isUTerm hi]
    rcases term_var (hv.nth hi).isUTerm with ⟨z, hz⟩ | ⟨x, hx⟩
    · have hzn : z < n := by simpa [hz] using hv.nth hi
      rw [hz, termSubst_bvar, termSubst_bvar, H z hzn]
    · rw [hx, termSubst_fvar, termSubst_fvar]
  · intro n l M w l' M' w' _ _ _ _ _; simp
  · intro n l M w l' M' w' _ _ _ _ _; simp
  · intro n p q hp hq ihp ihq l M w l' M' w' hw hw' hl hl' H
    rw [substs_and hp.isUFormula hq.isUFormula, substs_and hp.isUFormula hq.isUFormula,
      ihp l M w l' M' w' hw hw' hl hl' H, ihq l M w l' M' w' hw hw' hl hl' H]
  · intro n p q hp hq ihp ihq l M w l' M' w' hw hw' hl hl' H
    rw [substs_or hp.isUFormula hq.isUFormula, substs_or hp.isUFormula hq.isUFormula,
      ihp l M w l' M' w' hw hw' hl hl' H, ihq l M w l' M' w' hw hw' hl hl' H]
  · intro n p hp ih l M w l' M' w' hw hw' hl hl' H
    rw [substs_all hp.isUFormula, substs_all hp.isUFormula]
    congr 1
    refine ih (l + 1) (M + 1) (qVec ℒₛₑₜ w) (l' + 1) (M' + 1) (qVec ℒₛₑₜ w') hw.qVec hw'.qVec
      (_root_.add_le_add hl le_rfl) (_root_.add_le_add hl' le_rfl) ?_
    intro i hi
    rcases zero_or_succ i with rfl | ⟨j, rfl⟩
    · simp [qVec]
    · have hj : j < n := by simpa using hi
      simp only [qVec, nth_adjoin_succ]
      rw [hw.lh, hw'.lh, nth_termBShiftVec hw.isUTerm (lt_of_lt_of_le hj hl),
        nth_termBShiftVec hw'.isUTerm (lt_of_lt_of_le hj hl'), H j hj]
  · intro n p hp ih l M w l' M' w' hw hw' hl hl' H
    rw [substs_ex hp.isUFormula, substs_ex hp.isUFormula]
    congr 1
    refine ih (l + 1) (M + 1) (qVec ℒₛₑₜ w) (l' + 1) (M' + 1) (qVec ℒₛₑₜ w') hw.qVec hw'.qVec
      (_root_.add_le_add hl le_rfl) (_root_.add_le_add hl' le_rfl) ?_
    intro i hi
    rcases zero_or_succ i with rfl | ⟨j, rfl⟩
    · simp [qVec]
    · have hj : j < n := by simpa using hi
      simp only [qVec, nth_adjoin_succ]
      rw [hw.lh, hw'.lh, nth_termBShiftVec hw.isUTerm (lt_of_lt_of_le hj hl),
        nth_termBShiftVec hw'.isUTerm (lt_of_lt_of_le hj hl'), H j hj]

theorem subst_fvarVec_trunc {m N b : V} (hb : IsSemiformula ℒₛₑₜ m b) (hm : m ≤ N) :
    subst ℒₛₑₜ (fvarVec m) b = subst ℒₛₑₜ (fvarVec N) b :=
  subst_congr hb m 0 (fvarVec m) N 0 (fvarVec N) (ModelCodedBindFree.fvarVec_isTermVec m) (ModelCodedBindFree.fvarVec_isTermVec N) le_rfl hm
    (fun i hi => by rw [nth_fvarVec m i hi, nth_fvarVec N i (lt_of_lt_of_le hi hm)])

/-! ## Universal closures -/

theorem qqAlls_add (b m : V) : ∀ k : V, qqAlls b (m + k) = qqAlls (qqAlls b m) k := by
  intro k
  induction k using ISigma1.sigma1_succ_induction
  · definability
  · simp
  · case succ k ih => rw [← add_assoc, qqAlls_succ, qqAlls_succ, ih]

theorem allClosure_val : ∀ (n : ℕ) (φ : Bootstrapping.Semiformula V ℒₛₑₜ n),
    (∀⁰* φ).val = qqAlls φ.val (n : V)
  | 0, φ => by simp
  | n + 1, φ => by
      show (∀⁰* (∀⁰ φ)).val = _
      rw [allClosure_val n (∀⁰ φ), Bootstrapping.Semiformula.val_all]
      push_cast
      rw [qqAlls_succ']

theorem freshTuple_val (n : ℕ) : (freshTuple (V := V) (L := ℒₛₑₜ) n).val = fvarVec (n : V) := by
  have hv := (freshTuple (V := V) (L := ℒₛₑₜ) n).isSemitermVec
  apply nth_ext' (n : V) hv.lh (len_fvarVec _)
  intro i hi
  obtain ⟨j, rfl⟩ := eq_fin_of_lt_nat hi
  rw [Bootstrapping.SemitermVec.val_nth_eq, nth_fvarVec _ _ hi]
  simp [freshTuple]

/-! ## Vacuous generalization -/

theorem closed_qqAlls {X : V} (hX : IsSemiformula ℒₛₑₜ 0 X) (k : V) :
    IsSemiformula ℒₛₑₜ 0 (qqAlls X k) :=
  IsSemiformula.qqAlls ⟨hX.isUFormula, le_trans hX.bv_le (by simp)⟩

theorem shift_qqAlls' {X : V} (hX : IsUFormula ℒₛₑₜ X) (hs : shift ℒₛₑₜ X = X) (k : V) :
    shift ℒₛₑₜ (qqAlls X k) = qqAlls X k := by
  rw [ModelCodedRenamingAxioms.shift_qqAlls hX, hs]

set_option maxHeartbeats 1000000 in
/-- **Vacuous generalization, bounded**: a closed shift-fixed formula `X`
gives `∀^k X` at two levels per binder. -/
theorem vac_gen {X w : V} (hX : IsSemiformula ℒₛₑₜ 0 X) (hs : shift ℒₛₑₜ X = X) (hw : 4 ≤ w)
    (h : DLv 𝗭𝗙 (insert X ∅) w) : ∀ k : V, (∀ j ≤ k, qqAlls X j < lvB w) →
      DLv 𝗭𝗙 (insert (qqAlls X k) ∅) (w + 2 * k) := by
  intro k
  induction k using ISigma1.pi1_succ_induction
  · simp only [DLv, DerivableLe, lvB]
    definability
  · intro _; simpa using h
  · case succ k ih =>
    intro hb
    have d := ih (fun j hj => hb j (le_trans hj le_self_add))
    set Y := qqAlls X k with hY
    have hYc : IsSemiformula ℒₛₑₜ 0 Y := closed_qqAlls hX k
    have hYs : shift ℒₛₑₜ Y = Y := shift_qqAlls' hX.isUFormula hs k
    have hall : qqAlls X (k + 1) = ^∀ Y := qqAlls_succ X k
    have lY : Y < lvB w := hb k le_self_add
    have lA : ^∀ Y < lvB w := hall ▸ hb (k + 1) le_rfl
    have hw' : w ≤ w + 2 * k := le_self_add
    have hS : setShift ℒₛₑₜ (insert (^∀ Y) (∅ : V)) = insert (^∀ Y) ∅ := by
      rw [mem_setShift_insert, Bootstrapping.shift_all hYc.isUFormula, hYs]
      congr 1
      exact mem_ext fun y => by simp [mem_setShift_iff]
    have hfA : IsFormula ℒₛₑₜ (^∀ Y) := by
      have := closed_qqAlls hX (k + 1); rwa [hall] at this
    have d1 : DLv 𝗭𝗙 (insert Y (insert (^∀ Y) ∅)) (w + 2 * k + 1) :=
      DLv.wk (le_trans hw hw') ((((SeqLt.empty _).insert lA).insert lY).mono hw')
        (by simp [hYc, hfA]) (insert_subset_insert_of_subset _ (by intro z hz; simp at hz)) d
    have d2 := DLv.all_m (le_trans hw (le_trans hw' le_self_add))
      (((SeqLt.empty _).insert lA).mono (le_trans hw' le_self_add)) (p := Y) (by simp)
      (by rw [hS, free_closed hYc hYs]; exact d1)
    rw [hall, show w + 2 * (k + 1) = w + 2 * k + 1 + 1 by ring]
    exact d2

/-! ## Recognized schema axioms are `𝗭𝗙` axioms -/

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
theorem union_class_iff' (T U : Theory ℒₛₑₜ) [T.Δ₁] [U.Δ₁] (p : V) :
    p ∈ (T ∪ U).Δ₁Class ↔ p ∈ T.Δ₁Class ∨ p ∈ U.Δ₁Class := by
  change (V ⊧/![p] (T.Δ₁ch ⋎ U.Δ₁ch).val) ↔
    (V ⊧/![p] T.Δ₁ch.val) ∨ (V ⊧/![p] U.Δ₁ch.val)
  rw [HierarchySymbol.Semiformula.val_or]
  simp only [LogicalConnective.HomClass.map_or, LogicalConnective.Prop.or_eq]

theorem sepR_mem_zf {p : V} (h : SepR p) : p ∈ (𝗭𝗙 : SetTheory).Δ₁Class := by
  change p ∈ (((𝗘𝗤 ℒₛₑₜ ∪ zfFixed) ∪ separationTheory) ∪ replacementTheory).Δ₁Class
  rw [union_class_iff', union_class_iff', union_class_iff']
  refine Or.inl (Or.inr ?_)
  change (V ⊧/![p] sepCh.val)
  simpa using h

theorem repR_mem_zf {p : V} (h : RepR p) : p ∈ (𝗭𝗙 : SetTheory).Δ₁Class := by
  change p ∈ (((𝗘𝗤 ℒₛₑₜ ∪ zfFixed) ∪ separationTheory) ∪ replacementTheory).Δ₁Class
  rw [union_class_iff']
  refine Or.inr ?_
  change (V ⊧/![p] repCh.val)
  simpa using h

/-! ## The generic schema leaf -/

variable {k : ℕ} {arities : Fin k → ℕ}

theorem shiftedPredicates_fixed (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    (hKs : ∀ i, (Ks i).shift = Ks i) : ∀ b, shiftedPredicates Ks b = Ks
  | 0 => rfl
  | b + 1 => by
      funext i
      simp only [shiftedPredicates, shiftedPredicates_fixed Ks hKs b, hKs]

theorem shifts_fixed {n : ℕ} (T : Bootstrapping.Semiformula V ℒₛₑₜ n) (hT : T.shift = T) :
    ∀ b, shifts b T = T
  | 0 => rfl
  | b + 1 => by simp only [shifts, shifts_fixed T hT b, hT]

theorem sourceClosure_shift (q : Proposition (setTemplateLanguage k arities)) :
    Rewriting.shift (sourceClosure q) = sourceClosure q := by
  apply FirstOrder.Semiformula.rew_eq_self_of
  · simp
  · intro x hx
    simp [FirstOrder.Semiformula.FVar?, sourceClosure_closed q] at hx

set_option maxHeartbeats 1000000 in
/-- **The bounded schema leaf.** For shift-fixed placeholders at level `u`,
the translated universal closure of a schema instance has a `𝗭𝗙`-derivation
at level `tA·(u+1) + 2N + 5`, `N` the instance's free-variable count. -/
theorem schema_leaf {a : ℕ}
    (src : Semiproposition (setTemplateLanguage k arities) a → Proposition (setTemplateLanguage k arities))
    (body : Bootstrapping.Semiformula V ℒₛₑₜ a → Bootstrapping.Formula V ℒₛₑₜ) (bodyVal : V → V)
    (htr : ∀ (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i)) p,
      translateFormula Ks (src p) = body (translateFormula Ks p))
    (hval : ∀ K, bodyVal K.val = (body K).val)
    (hle : ∀ K : Bootstrapping.Semiformula V ℒₛₑₜ a, K.val ≤ (body K).val)
    (hmem : ∀ x : V, SchemaRecognizer ℒₛₑₜ a bodyVal x → x ∈ (𝗭𝗙 : SetTheory).Δ₁Class)
    (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    (hKs : ∀ i, (Ks i).shift = Ks i) {u : V} (hK : ∀ i, (Ks i).val ≤ lvB u)
    (p : Semiproposition (setTemplateLanguage k arities) a) :
    DLv 𝗭𝗙 (insert (translateFormula Ks (Rewriting.emb (src p).univCl)).val ∅)
      ((tA (Rewriting.emb (src p).univCl : Proposition (setTemplateLanguage k arities)) : V) *
        (u + 1) + 5 + 2 * ((0 + (src p).fvSup : ℕ) : V)) := by
  set σ := src p with hσ
  set T := translateFormula Ks (sourceClosure σ) with hTdef
  have hTs : T.shift = T := by
    rw [hTdef, ← translateFormula_shift Ks hKs, sourceClosure_shift]
  have hTsv : shift ℒₛₑₜ T.val = T.val := by
    have := congrArg Bootstrapping.Semiformula.val hTs
    simpa using this
  have hΦv : (translateFormula Ks (Rewriting.emb σ.univCl)).val =
      qqAlls T.val ((0 + σ.fvSup : ℕ) : V) := by
    rw [translate_univCl, allClosure_val]
  have hopen : subst ℒₛₑₜ (fvarVec ((0 + σ.fvSup : ℕ) : V)) T.val = (body (translateFormula Ks p)).val := by
    have h := closure_opening Ks σ
    rw [shifts_fixed T hTs, shiftedPredicates_fixed Ks hKs] at h
    have h' := h.trans (htr Ks p)
    rw [← freshTuple_val, ← Bootstrapping.Semiformula.val_substs, h']
  set N : V := ((0 + σ.fvSup : ℕ) : V) with hN
  set m := bv ℒₛₑₜ T.val with hm
  have hTm : IsSemiformula ℒₛₑₜ m T.val := ⟨T.isSemiformula.isUFormula, le_rfl⟩
  have hmN : m ≤ N := T.isSemiformula.bv_le
  have hopen_m : subst ℒₛₑₜ (fvarVec m) T.val = bodyVal (translateFormula Ks p).val := by
    rw [subst_fvarVec_trunc hTm hmN, hopen, hval]
  have hrec : SchemaRecognizer ℒₛₑₜ a bodyVal (qqAlls T.val m) :=
    ⟨m, index_le_qqAlls _ _, T.val, le_qqAlls _ _, rfl, T.isSemiformula.isUFormula, hTsv, rfl,
      (translateFormula Ks p).val, by rw [hopen_m, hval]; exact hle _,
      (translateFormula Ks p).isSemiformula, hopen_m⟩
  set Ψ := qqAlls T.val m with hΨ
  have hΨmem : Ψ ∈ (𝗭𝗙 : SetTheory).Δ₁Class := hmem _ hrec
  have hΨc : IsSemiformula ℒₛₑₜ 0 Ψ := IsSemiformula.qqAlls (by simpa using hTm)
  have hΨs : shift ℒₛₑₜ Ψ = Ψ := shift_qqAlls' T.isSemiformula.isUFormula hTsv m
  have hsplit : qqAlls T.val N = qqAlls Ψ (N - m) := by
    rw [hΨ, ← qqAlls_add, add_tsub_cancel_of_le hmN]
  -- levels
  set Lφ : V := (tA (Rewriting.emb σ.univCl : Proposition (setTemplateLanguage k arities)) : V) *
    (u + 1) with hLφ
  have hΦl : qqAlls Ψ (N - m) ≤ lvB Lφ := by
    rw [← hsplit, ← hΦv]
    exact translate_level _ u Ks hK
  have hsub : ∀ j ≤ N - m, qqAlls Ψ j ≤ qqAlls Ψ (N - m) := fun j hj => by
    rw [show N - m = j + (N - m - j) from (add_tsub_cancel_of_le hj).symm, qqAlls_add]
    exact le_qqAlls _ _
  have hw4 : 4 ≤ Lφ + 4 := le_add_self
  have d0 : DLv 𝗭𝗙 (insert Ψ ∅) (Lφ + 4 + 1) :=
    DLv.by_axm hw4 ((SeqLt.empty _).insert (lt_lvB_of (le_trans (le_qqAlls Ψ (N - m)) hΦl)
      (_root_.add_le_add le_rfl (by norm_num))))
      (by simp [hΨc]) Ψ (by simp) hΨmem
  have d1 := vac_gen hΨc hΨs (le_trans hw4 le_self_add) d0 (N - m) (fun j hj =>
    lt_lvB_of (le_trans (hsub j hj) hΦl) (le_trans (_root_.add_le_add le_rfl (by norm_num))
      le_self_add))
  rw [hΦv, hsplit]
  refine d1.mono ?_
  rw [show Lφ + 4 + 1 = Lφ + 5 by ring]
  exact _root_.add_le_add le_rfl (mul_le_mul_of_nonneg_left tsub_le_self (by norm_num))

theorem sep_le (K : Bootstrapping.Semiformula V ℒₛₑₜ 1) : K.val ≤ (sepBody K).val := by
  have h := subst_le_sepBodyVal K.val
  rwa [ModelCodedSchemaAxioms.sep_core_subst_identity K, sepBodyVal_eq K] at h

theorem rep_le (K : Bootstrapping.Semiformula V ℒₛₑₜ 2) : K.val ≤ (repBody K).val := by
  have h := subst3_le_repBodyVal K.val
  rwa [ModelCodedSchemaAxioms.rep_core_subst_identity K, repBodyVal_eq K] at h

/-- **The separation leaf, bounded.** -/
theorem sep_leaf (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    (hKs : ∀ i, (Ks i).shift = Ks i) {u : V} (hK : ∀ i, (Ks i).val ≤ lvB u)
    (p : Semiproposition (setTemplateLanguage k arities) 1) :
    DLv 𝗭𝗙 (insert (translateFormula Ks
        (Rewriting.emb (OpenSchemaTemplates.sepBodySource p).univCl)).val ∅)
      ((tA (Rewriting.emb (OpenSchemaTemplates.sepBodySource p).univCl :
          Proposition (setTemplateLanguage k arities)) : V) * (u + 1) + 5 +
        2 * ((0 + (OpenSchemaTemplates.sepBodySource p).fvSup : ℕ) : V)) :=
  schema_leaf OpenSchemaTemplates.sepBodySource sepBody sepBodyVal
    (fun Ks p => OpenSchemaTemplates.translate_sepBodySource Ks p) sepBodyVal_eq sep_le
    (fun _ h => sepR_mem_zf h) Ks hKs hK p

/-- **The replacement leaf, bounded.** -/
theorem rep_leaf (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    (hKs : ∀ i, (Ks i).shift = Ks i) {u : V} (hK : ∀ i, (Ks i).val ≤ lvB u)
    (p : Semiproposition (setTemplateLanguage k arities) 2) :
    DLv 𝗭𝗙 (insert (translateFormula Ks
        (Rewriting.emb (OpenSchemaTemplates.repBodySource p).univCl)).val ∅)
      ((tA (Rewriting.emb (OpenSchemaTemplates.repBodySource p).univCl :
          Proposition (setTemplateLanguage k arities)) : V) * (u + 1) + 5 +
        2 * ((0 + (OpenSchemaTemplates.repBodySource p).fvSup : ℕ) : V)) :=
  schema_leaf OpenSchemaTemplates.repBodySource repBody repBodyVal
    (fun Ks p => OpenSchemaTemplates.translate_repBodySource Ks p) repBodyVal_eq rep_le
    (fun _ h => repR_mem_zf h) Ks hKs hK p

end LeanProofs.ZFCinPA.SizedSchemaLeaves
