import ZFCinPA.LGlueCodes
import ZFCinPA.SeparationDelta1
import ZFCinPA.ReplacementDelta1

set_option autoImplicit false
noncomputable section

/-!
# Free-variable bounds for schema cores

The schema recognizer hands over a shift-fixed body `b` of level `m` whose
free-ized instance `subst (fvarVec m) b` is the separation (or replacement)
body of a core `K`. The glue needs the free variables of `K` (freed at its
bound slots) to lie below `m + 1` (resp. `m + 2`). Two code lemmas give that:

* `bindFreeAt_subst_opening`: binding the free variables back after an
  opening substitution recovers a shift-fixed formula, so
  `FvLt m (subst (fvarVec m) b)` (`fvLt_subst_fvarVec`);
* `fvBound_subst`: a substitution by bound variables only cannot hide free
  variables, so the bound on the substituted core passes to the core itself.

`sep_core_bound` and `repl_core_bound` read them off the two skeletons.
-/

namespace LeanProofs.ZFCinPA.LFvBound

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.ZFCinPA LeanProofs.ZFCinPA.ModelCodedBindFree LeanProofs.ZFCinPA.LGlueCodes
open scoped LO.FirstOrder.Arithmetic

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private instance opening_definable' : 𝚫₁-Relation₃[V] (Opening (V := V)) := by
  unfold Opening
  definability

private instance bindFreeAt_delta' : 𝚫₁-Function₂[V] (bindFreeAt (V := V) ℒₛₑₜ) :=
  bindFreeAt_defined.graph_delta.to_definable

/-! ## Binding after an opening substitution -/

lemma bind_subst_opening_term {n d w t : V} (ht : IsSemiterm ℒₛₑₜ n t)
    (hs : termShift ℒₛₑₜ t = t) (ho : Opening d n w) :
    termBindFreeAt ℒₛₑₜ d (termSubst ℒₛₑₜ w t) = t := by
  rcases semiterm_cases ht with ⟨z, hz, rfl⟩ | ⟨x, rfl⟩
  · rw [termSubst_bvar]
    rcases lt_or_ge z d with hzd | hzd
    · rw [ho.2.1 z hzd, termBindFreeAt_bvar]
    · obtain ⟨x, rfl⟩ := exists_add_of_le hzd
      have hx : x < n := lt_of_le_of_lt (by simp) hz
      rw [ho.2.2 x hx hz, termBindFreeAt_fvar]
  · simp at hs

lemma bindVec_subst_opening {n d w k v : V} (hv : IsSemitermVec ℒₛₑₜ k n v)
    (hs : termShiftVec ℒₛₑₜ k v = v) (hw : IsSemitermVec ℒₛₑₜ n d w) (ho : Opening d n w) :
    termBindFreeVecAt ℒₛₑₜ d k (termSubstVec ℒₛₑₜ k w v) = v := by
  have hsv : IsUTermVec ℒₛₑₜ k (termSubstVec ℒₛₑₜ k w v) :=
    (IsSemitermVec.termSubstVec hw hv).isUTerm
  apply nth_ext' k (termBindFreeVecAt_lh _ hsv) hv.lh
  intro i hi
  rw [nth_termBindFreeVecAt _ hsv hi, nth_termSubstVec hv.isUTerm hi]
  have hsi : termShift ℒₛₑₜ v.[i] = v.[i] := by
    have h := congrArg (fun u ↦ u.[i]) hs
    simpa [nth_termShiftVec hv.isUTerm hi] using h
  exact bind_subst_opening_term (hv.nth hi) hsi ho

/-- Binding the free variables back after an opening substitution recovers a
shift-fixed formula. -/
theorem bindFreeAt_subst_opening {n b : V} (hb : IsSemiformula ℒₛₑₜ n b) :
    shift ℒₛₑₜ b = b → ∀ d w : V, IsSemitermVec ℒₛₑₜ n d w → Opening d n w →
      bindFreeAt ℒₛₑₜ d (subst ℒₛₑₜ w b) = b := by
  refine IsSemiformula.pi1_structural_induction (L := ℒₛₑₜ)
    (P := fun n b ↦ shift ℒₛₑₜ b = b → ∀ d w : V, IsSemitermVec ℒₛₑₜ n d w → Opening d n w →
      bindFreeAt ℒₛₑₜ d (subst ℒₛₑₜ w b) = b)
    (by definability) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hb
  · intro n k R v hR hv hs d w hw ho
    rw [shift_rel hR hv.isUTerm, qqRel_inj] at hs
    have hsv := IsSemitermVec.termSubstVec hw hv
    rw [substs_rel hR hv.isUTerm, bindFreeAt_rel _ hR hsv.isUTerm,
      bindVec_subst_opening hv hs.2.2 hw ho]
  · intro n k R v hR hv hs d w hw ho
    rw [shift_nrel hR hv.isUTerm, qqNRel_inj] at hs
    have hsv := IsSemitermVec.termSubstVec hw hv
    rw [substs_nrel hR hv.isUTerm, bindFreeAt_nrel _ hR hsv.isUTerm,
      bindVec_subst_opening hv hs.2.2 hw ho]
  · intro n _ d w _ _
    simp
  · intro n _ d w _ _
    simp
  · intro n p q hp hq ihp ihq hs d w hw ho
    rw [shift_and hp.isUFormula hq.isUFormula, qqAnd_inj] at hs
    rw [substs_and hp.isUFormula hq.isUFormula,
      bindFreeAt_and _ (hp.subst hw).isUFormula (hq.subst hw).isUFormula,
      ihp hs.1 d w hw ho, ihq hs.2 d w hw ho]
  · intro n p q hp hq ihp ihq hs d w hw ho
    rw [shift_or hp.isUFormula hq.isUFormula, qqOr_inj] at hs
    rw [substs_or hp.isUFormula hq.isUFormula,
      bindFreeAt_or _ (hp.subst hw).isUFormula (hq.subst hw).isUFormula,
      ihp hs.1 d w hw ho, ihq hs.2 d w hw ho]
  · intro n p hp ih hs d w hw ho
    rw [shift_all hp.isUFormula, qqAll_inj] at hs
    rw [substs_all hp.isUFormula, bindFreeAt_all _ (hp.subst hw.qVec).isUFormula,
      ih hs (d + 1) (qVec ℒₛₑₜ w) hw.qVec (ho.qVec hw)]
  · intro n p hp ih hs d w hw ho
    rw [shift_exs hp.isUFormula, qqExs_inj] at hs
    rw [substs_ex hp.isUFormula, bindFreeAt_exs _ (hp.subst hw.qVec).isUFormula,
      ih hs (d + 1) (qVec ℒₛₑₜ w) hw.qVec (ho.qVec hw)]

/-- The free-ized instance of a shift-fixed level-`m` body has its free
variables below `m`. -/
theorem fvLt_subst_fvarVec {m b : V} (hb : IsSemiformula ℒₛₑₜ m b) (hs : shift ℒₛₑₜ b = b) :
    FvLt m (subst ℒₛₑₜ (fvarVec m) b) := by
  unfold FvLt
  rw [bindFreeAt_subst_opening hb hs 0 (fvarVec m) (fvarVec_isTermVec (L := ℒₛₑₜ) m)
    ⟨by simp, by simp, fun x hx _ ↦ by simpa using nth_fvarVec m x hx⟩]
  exact hb

/-! ## Substitutions by bound variables -/

/-- Every entry of `w` (below `a`) is a bound variable below `n`. -/
def BvOnly (n a w : V) : Prop := ∀ i < a, ∃ z < n, w.[i] = ^#z

private instance bvOnly_definable : 𝚫₁-Relation₃[V] (BvOnly (V := V)) := by
  unfold BvOnly
  definability

lemma bvOnly_qVec {n a w : V} (hb : BvOnly n a w) (hw : IsSemitermVec ℒₛₑₜ a n w) :
    BvOnly (n + 1) (a + 1) (qVec ℒₛₑₜ w) := by
  intro i hi
  rcases zero_or_succ i with rfl | ⟨i, rfl⟩
  · exact ⟨0, by simp, by simp [Bootstrapping.qVec]⟩
  · have hi' : i < a := by simpa using hi
    obtain ⟨z, hz, hwz⟩ := hb i hi'
    refine ⟨z + 1, by simpa using hz, ?_⟩
    simp only [Bootstrapping.qVec, hw.lh, nth_adjoin_succ]
    rw [nth_termBShiftVec hw.isUTerm hi', hwz]
    simp

lemma fvBound_term {a n j w t : V} (ht : IsSemiterm ℒₛₑₜ a t) (hw : BvOnly n a w)
    (h : IsSemiterm ℒₛₑₜ (j + n) (termBindFreeAt ℒₛₑₜ n (termSubst ℒₛₑₜ w t))) :
    IsSemiterm ℒₛₑₜ (j + a) (termBindFreeAt ℒₛₑₜ a t) := by
  rcases semiterm_cases ht with ⟨z, hz, rfl⟩ | ⟨x, rfl⟩
  · rw [termBindFreeAt_bvar]
    simpa using lt_of_lt_of_le hz (show a ≤ j + a by simp)
  · rw [termSubst_fvar, termBindFreeAt_fvar] at h
    rw [termBindFreeAt_fvar]
    have h' : n + x < n + j := by simpa [add_comm j n] using h
    have hx : x < j := lt_of_add_lt_add_left h'
    have : x + a < j + a := add_lt_add_left hx a
    simpa [add_comm x a] using this

lemma fvBound_vec {a n j w k v : V} (hv : IsSemitermVec ℒₛₑₜ k a v) (hb : BvOnly n a w)
    (hw : IsSemitermVec ℒₛₑₜ a n w)
    (h : IsSemitermVec ℒₛₑₜ k (j + n) (termBindFreeVecAt ℒₛₑₜ n k (termSubstVec ℒₛₑₜ k w v))) :
    IsSemitermVec ℒₛₑₜ k (j + a) (termBindFreeVecAt ℒₛₑₜ a k v) := by
  have hsv : IsUTermVec ℒₛₑₜ k (termSubstVec ℒₛₑₜ k w v) :=
    (IsSemitermVec.termSubstVec hw hv).isUTerm
  refine IsSemitermVec.iff.mpr ⟨termBindFreeVecAt_lh _ hv.isUTerm, fun i hi ↦ ?_⟩
  rw [nth_termBindFreeVecAt _ hv.isUTerm hi]
  have hi' := h.nth hi
  rw [nth_termBindFreeVecAt _ hsv hi, nth_termSubstVec hv.isUTerm hi] at hi'
  exact fvBound_term (hv.nth hi) hb hi'

/-- A substitution by bound variables only cannot hide free variables. -/
theorem fvBound_subst {a p : V} (hp : IsSemiformula ℒₛₑₜ a p) :
    ∀ n w j : V, IsSemitermVec ℒₛₑₜ a n w → BvOnly n a w →
      IsSemiformula ℒₛₑₜ (j + n) (bindFreeAt ℒₛₑₜ n (subst ℒₛₑₜ w p)) →
      IsSemiformula ℒₛₑₜ (j + a) (bindFreeAt ℒₛₑₜ a p) := by
  refine IsSemiformula.pi1_structural_induction (L := ℒₛₑₜ)
    (P := fun a p ↦ ∀ n w j : V, IsSemitermVec ℒₛₑₜ a n w → BvOnly n a w →
      IsSemiformula ℒₛₑₜ (j + n) (bindFreeAt ℒₛₑₜ n (subst ℒₛₑₜ w p)) →
      IsSemiformula ℒₛₑₜ (j + a) (bindFreeAt ℒₛₑₜ a p))
    (by definability) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · intro a k R v hR hv n w j hw hb h
    have hsv := IsSemitermVec.termSubstVec hw hv
    rw [substs_rel hR hv.isUTerm, bindFreeAt_rel _ hR hsv.isUTerm] at h
    rw [bindFreeAt_rel _ hR hv.isUTerm]
    simp only [IsSemiformula.rel] at h ⊢
    exact ⟨h.1, fvBound_vec hv hb hw h.2⟩
  · intro a k R v hR hv n w j hw hb h
    have hsv := IsSemitermVec.termSubstVec hw hv
    rw [substs_nrel hR hv.isUTerm, bindFreeAt_nrel _ hR hsv.isUTerm] at h
    rw [bindFreeAt_nrel _ hR hv.isUTerm]
    simp only [IsSemiformula.nrel] at h ⊢
    exact ⟨h.1, fvBound_vec hv hb hw h.2⟩
  · intro a n w j _ _ _
    simp
  · intro a n w j _ _ _
    simp
  · intro a p q hp hq ihp ihq n w j hw hb h
    rw [substs_and hp.isUFormula hq.isUFormula,
      bindFreeAt_and _ (hp.subst hw).isUFormula (hq.subst hw).isUFormula] at h
    rw [bindFreeAt_and _ hp.isUFormula hq.isUFormula]
    simp only [IsSemiformula.and] at h ⊢
    exact ⟨ihp n w j hw hb h.1, ihq n w j hw hb h.2⟩
  · intro a p q hp hq ihp ihq n w j hw hb h
    rw [substs_or hp.isUFormula hq.isUFormula,
      bindFreeAt_or _ (hp.subst hw).isUFormula (hq.subst hw).isUFormula] at h
    rw [bindFreeAt_or _ hp.isUFormula hq.isUFormula]
    simp only [IsSemiformula.or] at h ⊢
    exact ⟨ihp n w j hw hb h.1, ihq n w j hw hb h.2⟩
  · intro a p hp ih n w j hw hb h
    rw [substs_all hp.isUFormula, bindFreeAt_all _ (hp.subst hw.qVec).isUFormula] at h
    rw [bindFreeAt_all _ hp.isUFormula]
    simp only [IsSemiformula.all] at h ⊢
    have := ih (n + 1) (qVec ℒₛₑₜ w) j hw.qVec (bvOnly_qVec hb hw) (by rwa [← add_assoc])
    rwa [add_assoc]
  · intro a p hp ih n w j hw hb h
    rw [substs_ex hp.isUFormula, bindFreeAt_exs _ (hp.subst hw.qVec).isUFormula] at h
    rw [bindFreeAt_exs _ hp.isUFormula]
    simp only [IsSemiformula.exs] at h ⊢
    have := ih (n + 1) (qVec ℒₛₑₜ w) j hw.qVec (bvOnly_qVec hb hw) (by rwa [← add_assoc])
    rwa [add_assoc]

/-- `FvLt (j + 1) (free p)` reads the bound of `p` at depth one. -/
lemma fvLt_free_iff {j p : V} (hp : IsSemiformula ℒₛₑₜ 1 p) :
    FvLt (j + 1) (free ℒₛₑₜ p) ↔ IsSemiformula ℒₛₑₜ (j + 1) (bindFreeAt ℒₛₑₜ 1 p) := by
  have h1 := bindFreeAt_open hp _root_.one_ne_zero
  simp only [show (1 : V) - 1 = 0 by simp] at h1
  unfold FvLt
  rw [← h1]
  simp [free, substs1, openVec]

/-! ## The two skeletons -/

/-- The separation core: the bound on the body passes to `free K`. -/
theorem sep_core_bound {m K : V} (hK : IsSemiformula ℒₛₑₜ 1 K) (h : FvLt m (sepBodyVal K)) :
    FvLt (m + 1) (free ℒₛₑₜ K) := by
  let Kt : Bootstrapping.Semiformula V ℒₛₑₜ 1 := ⟨K, by simpa using hK⟩
  let w : Bootstrapping.SemitermVec V ℒₛₑₜ 1 3 := ![⌜(#0 : SyntacticSemiterm ℒₛₑₜ 3)⌝]
  let ZY : Bootstrapping.Semiformula V ℒₛₑₜ 3 := ⌜sepAtomZY⌝
  let ZX : Bootstrapping.Semiformula V ℒₛₑₜ 3 := ⌜sepAtomZX⌝
  have hval : sepBodyVal K =
      ^∀ ^∃ ^∀ (Bootstrapping.iff ℒₛₑₜ ZY.val (ZX.val ^⋏ subst ℒₛₑₜ w.val K)) := by
    simp only [sepBodyVal, ZY, ZX, w, val_sepAtomZY, val_sepAtomZX, val_sepSubstConst]
  have hZY : IsSemiformula ℒₛₑₜ 3 ZY.val := by simpa using ZY.isSemiformula
  have hZX : IsSemiformula ℒₛₑₜ 3 ZX.val := by simpa using ZX.isSemiformula
  have hS : IsSemiformula ℒₛₑₜ 3 (subst ℒₛₑₜ w.val K) := by simpa using (Kt.subst w).isSemiformula
  have hw : IsSemitermVec ℒₛₑₜ 1 3 w.val := by simpa using w.isSemitermVec
  have hb : BvOnly 3 1 w.val := by
    intro i hi
    have hi0 : i = 0 := by simpa using hi
    subst hi0
    exact ⟨0, by simp, by simp [w, Bootstrapping.SemitermVec.val]⟩
  let T : Bootstrapping.Semiformula V ℒₛₑₜ 3 := ZY 🡘 (ZX ⋏ Kt.subst w)
  have hT : T.val = Bootstrapping.iff ℒₛₑₜ ZY.val (ZX.val ^⋏ subst ℒₛₑₜ w.val K) := by
    simp [T, Kt]
  have hT1 : IsSemiformula ℒₛₑₜ 3 (Bootstrapping.iff ℒₛₑₜ ZY.val (ZX.val ^⋏ subst ℒₛₑₜ w.val K)) := by
    rw [← hT]; simpa using T.isSemiformula
  have hT2 := hT1.isUFormula
  generalize w.val = W at hval hS hw hb hT1 hT2
  have e3 : ((0 : V) + 1 + 1 + 1) = 3 := by norm_num
  have em : (m + 1 + 1 + 1) = m + 3 := by rw [← e3]; simp only [zero_add, ← add_assoc]
  have hd : (1 : V) + 1 + 1 = 3 := by norm_num
  have hXS : IsUFormula ℒₛₑₜ (ZX.val ^⋏ subst ℒₛₑₜ W K) := by
    simp [hZX.isUFormula, hS.isUFormula]
  unfold FvLt at h
  rw [hval, bindFreeAt_all _ (by simp [hT2]), bindFreeAt_exs _ (by simp [hT2]),
    bindFreeAt_all _ hT2] at h
  simp only [IsSemiformula.all, IsSemiformula.exs, zero_add] at h
  rw [em, hd, Bootstrapping.iff, Bootstrapping.imp, Bootstrapping.imp,
    bindFreeAt_and _ (by simp [hZY.isUFormula.neg, hXS]) (by simp [hXS.neg, hZY.isUFormula])] at h
  simp only [IsSemiformula.and] at h
  have h1 := h.1
  rw [bindFreeAt_or _ hZY.isUFormula.neg hXS] at h1
  simp only [IsSemiformula.or] at h1
  have h2 := h1.2
  rw [bindFreeAt_and _ hZX.isUFormula hS.isUFormula] at h2
  simp only [IsSemiformula.and] at h2
  rw [fvLt_free_iff hK]
  exact fvBound_subst hK 3 W m hw hb h2.2

/-- The replacement core: the bound on the body passes to `K` at depth two. -/
theorem repl_core_bound {m K : V} (hK : IsSemiformula ℒₛₑₜ 2 K) (h : FvLt m (repBodyVal K)) :
    IsSemiformula ℒₛₑₜ (m + 2) (bindFreeAt ℒₛₑₜ 2 K) := by
  let Kt : Bootstrapping.Semiformula V ℒₛₑₜ 2 := ⟨K, by simpa using hK⟩
  let w1 : Bootstrapping.SemitermVec V ℒₛₑₜ 2 2 :=
    ![⌜(#1 : SyntacticSemiterm ℒₛₑₜ 2)⌝, ⌜(#0 : SyntacticSemiterm ℒₛₑₜ 2)⌝]
  let w2 : Bootstrapping.SemitermVec V ℒₛₑₜ 2 3 :=
    ![⌜(#2 : SyntacticSemiterm ℒₛₑₜ 3)⌝, ⌜(#0 : SyntacticSemiterm ℒₛₑₜ 3)⌝]
  let w3 : Bootstrapping.SemitermVec V ℒₛₑₜ 2 4 :=
    ![⌜(#0 : SyntacticSemiterm ℒₛₑₜ 4)⌝, ⌜(#1 : SyntacticSemiterm ℒₛₑₜ 4)⌝]
  let EQ : Bootstrapping.Semiformula V ℒₛₑₜ 3 := ⌜repAtomEq⌝
  let YY : Bootstrapping.Semiformula V ℒₛₑₜ 3 := ⌜repAtomYY⌝
  let XX : Bootstrapping.Semiformula V ℒₛₑₜ 4 := ⌜repAtomXX⌝
  have hval : repBodyVal K = Bootstrapping.imp ℒₛₑₜ
      (^∀ ^∃ (subst ℒₛₑₜ w1.val K ^⋏ ^∀ (Bootstrapping.imp ℒₛₑₜ (subst ℒₛₑₜ w2.val K) EQ.val)))
      (^∀ ^∃ ^∀ (Bootstrapping.iff ℒₛₑₜ YY.val (^∃ (XX.val ^⋏ subst ℒₛₑₜ w3.val K)))) := by
    simp only [repBodyVal, EQ, YY, XX, w1, w2, w3, val_repAtomEq, val_repAtomYY, val_repAtomXX,
      val_repSubst1Const, val_repSubst2Const, val_repSubst3Const]
  let TA : Bootstrapping.Semiformula V ℒₛₑₜ 0 :=
    ∀⁰ ∃⁰ (Kt.subst w1 ⋏ (∀⁰ (Kt.subst w2 🡒 EQ)))
  let TB : Bootstrapping.Semiformula V ℒₛₑₜ 3 := YY 🡘 (∃⁰ (XX ⋏ Kt.subst w3))
  have hA : IsUFormula ℒₛₑₜ
      (^∀ ^∃ (subst ℒₛₑₜ w1.val K ^⋏ ^∀ (Bootstrapping.imp ℒₛₑₜ (subst ℒₛₑₜ w2.val K) EQ.val))) := by
    have e : TA.val = ^∀ ^∃ (subst ℒₛₑₜ w1.val K ^⋏
        ^∀ (Bootstrapping.imp ℒₛₑₜ (subst ℒₛₑₜ w2.val K) EQ.val)) := by simp [TA, Kt]
    rw [← e]; exact TA.isSemiformula.isUFormula
  have hB : IsUFormula ℒₛₑₜ (Bootstrapping.iff ℒₛₑₜ YY.val (^∃ (XX.val ^⋏ subst ℒₛₑₜ w3.val K))) := by
    have e : TB.val = Bootstrapping.iff ℒₛₑₜ YY.val (^∃ (XX.val ^⋏ subst ℒₛₑₜ w3.val K)) := by
      simp [TB, Kt]
    rw [← e]; exact TB.isSemiformula.isUFormula
  have hYY : IsSemiformula ℒₛₑₜ 3 YY.val := by simpa using YY.isSemiformula
  have hXX : IsSemiformula ℒₛₑₜ 4 XX.val := by simpa using XX.isSemiformula
  have hS : IsSemiformula ℒₛₑₜ 4 (subst ℒₛₑₜ w3.val K) := by
    simpa using (Kt.subst w3).isSemiformula
  have hw : IsSemitermVec ℒₛₑₜ 2 4 w3.val := by simpa using w3.isSemitermVec
  have hb : BvOnly 4 2 w3.val := by
    intro i hi
    rcases zero_or_succ i with rfl | ⟨i, rfl⟩
    · exact ⟨0, by simp, by simp [w3, Bootstrapping.SemitermVec.val]⟩
    · have h2 : i + 1 < 1 + 1 := by simpa [one_add_one_eq_two] using hi
      have h1 : i < 1 := lt_of_add_lt_add_right h2
      have hi0 : i = 0 := by simpa using h1
      subst hi0
      exact ⟨1, by simp, by simp [w3, Bootstrapping.SemitermVec.val]⟩
  generalize w3.val = W at hval hB hS hw hb
  have hXS : IsUFormula ℒₛₑₜ (XX.val ^⋏ subst ℒₛₑₜ W K) := by
    simp [hXX.isUFormula, hS.isUFormula]
  have hd3 : (0 : V) + 1 + 1 + 1 = 3 := by norm_num
  have em3 : m + 1 + 1 + 1 = m + 3 := by rw [← hd3]; simp only [zero_add, ← add_assoc]
  have hd4 : (3 : V) + 1 = 4 := by norm_num
  have em4 : m + 3 + 1 = m + 4 := by rw [← hd4, add_assoc]
  unfold FvLt at h
  rw [hval, Bootstrapping.imp, bindFreeAt_or _ hA.neg (by simp [hB])] at h
  simp only [IsSemiformula.or] at h
  have h1 := h.2
  rw [bindFreeAt_all _ (by simp [hB]), bindFreeAt_exs _ (by simp [hB]), bindFreeAt_all _ hB] at h1
  simp only [IsSemiformula.all, IsSemiformula.exs, zero_add] at h1
  rw [em3, show (1 : V) + 1 + 1 = 3 by rw [← hd3, zero_add], Bootstrapping.iff,
    Bootstrapping.imp, Bootstrapping.imp,
    bindFreeAt_and _ (by simp [hYY.isUFormula.neg, hXS]) (by simp [hXS, hYY.isUFormula])] at h1
  simp only [IsSemiformula.and] at h1
  have h2 := h1.1
  rw [bindFreeAt_or _ hYY.isUFormula.neg (by simp [hXS]), IsSemiformula.or] at h2
  have h3 := h2.2
  rw [bindFreeAt_exs _ hXS, IsSemiformula.exs, bindFreeAt_and _ hXX.isUFormula hS.isUFormula,
    IsSemiformula.and, em4, hd4] at h3
  exact fvBound_subst hK 4 W m hw hb h3.2

end LeanProofs.ZFCinPA.LFvBound
