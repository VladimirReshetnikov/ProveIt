import ZFCinPA.R2Main
import ZFCinPA.ValidatorNativeGicCongruence254

import ZFCinPA.ValidatorImplicationContext

set_option autoImplicit false
noncomputable section

namespace LeanProofs.ZFCinPA.R2Gic

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCode254
open LeanProofs.ZFCinPA.ValidatorProvability254 LeanProofs.ZFCinPA.ValidatorQuantifierCore254
open LeanProofs.ZFCinPA.ValidatorEnvironmentLabels254 LeanProofs.ZFCinPA.ValidatorEnvironmentVacuity254
open LeanProofs.ZFCinPA.ValidatorNativeGicSlots254 LeanProofs.ZFCinPA.ValidatorNativeGic254
open LeanProofs.ZFCinPA.R2Ctx LeanProofs.ZFCinPA.R2Neg LeanProofs.ZFCinPA.R2Quant
open scoped LO.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Typed encoder equations -/

abbrev SF (n : ℕ) := Bootstrapping.Semiformula V ℒₛₑₜ n

@[simp] lemma encT_all {n : ℕ} (F B s : V) (φ : SF (V := V) (n + 1)) :
    encode F B s (∀⁰ φ).val = wal s (encode F (s ∷ B) (s + 2) φ.val) :=
  encode_all F B s φ.isSemiformula.isUFormula
@[simp] lemma encT_exs {n : ℕ} (F B s : V) (φ : SF (V := V) (n + 1)) :
    encode F B s (∃⁰ φ).val = wim (wal s (wim (encode F (s ∷ B) (s + 2) φ.val) 1)) 1 :=
  encode_exs F B s φ.isSemiformula.isUFormula
@[simp] lemma encT_and {n : ℕ} (F B s : V) (φ ψ : SF (V := V) n) :
    encode F B s (φ ⋏ ψ).val = wim (wim (encode F B s φ.val) (wim (encode F B s ψ.val) 1)) 1 :=
  encode_and F B s φ.isSemiformula.isUFormula ψ.isSemiformula.isUFormula
@[simp] lemma encT_or {n : ℕ} (F B s : V) (φ ψ : SF (V := V) n) :
    encode F B s (φ ⋎ ψ).val = wim (wim (encode F B s φ.val) 1) (encode F B s ψ.val) :=
  encode_or F B s φ.isSemiformula.isUFormula ψ.isSemiformula.isUFormula
@[simp] lemma encT_imp {n : ℕ} (F B s : V) (φ ψ : SF (V := V) n) :
    encode F B s (φ 🡒 ψ).val =
      wim (wim (encode F B s (neg ℒₛₑₜ φ.val)) 1) (encode F B s ψ.val) := by
  rw [Bootstrapping.Semiformula.imp_def, encT_or, Bootstrapping.Semiformula.val_neg]

/-! ## Renaming one binder into a fresh label -/

open LeanProofs.ZFCinPA.ValidatorEqualityCore254 LeanProofs.ZFCinPA.ValidatorEqualityContext254
open LeanProofs.ZFCinPA.ValidatorEnvironmentAlpha254 LeanProofs.ZFCinPA.ValidatorEnvironmentStreams254
open LeanProofs.ZFCinPA.ValidatorEnvironmentSubstitution254

/-- `∀x A → ∀y B` from Leibniz at `x = y`, with `x` not free in `B` and `y` not
free in `∀x A`. -/
lemma all_rename {x y A B : V} (hL : CProv (wim (weq x y) (wim A B)))
    (vxB : Vac x B) (vy : Vac y (wal x A)) : CProv (wim (wal x A) (wal y B)) :=
  cProv_mp (all_relational 0 A B x y (cProv_mp (cProv_k _ 0) hL) (vac_truth x) vxB
    (vac_truth y) vy) cProv_truth

/-- `∃x A → ∃y B` from Leibniz at `x = y`, with `y` not free in `A` and `x` not
free in `∃y B`. -/
lemma ex_rename {x y A B : V} (hL : CProv (wim (weq x y) (wim A B)))
    (vyA : Vac y A) (vx : Vac x (ex y B)) : CProv (wim (ex x A) (ex y B)) := by
  have s0 : CProv (wim A (wim (weq y x) B)) :=
    ded2 (.mp (.mp (.ax hL) (.mp (.ax (eq_symm y x)) h0)) h1)
  have s1 : CProv (wim A (wal y (wim (weq y x) B))) := compose vyA (all_mono y s0)
  have s2 : CProv (wim (wal y (wim (weq y x) B)) (ex y B)) :=
    ded1 (.mp (.mp (.ax (all_imp_ex y (weq y x) B)) h0) (.ax (ex_equality y x)))
  exact compose (ex_mono x (compose s1 s2)) (ex_elim_of_vac vx)

/-- The two-slot equality context from its two equations. -/
lemma ctx2_intro (u v u' v' : V) :
    CProv (wim (weq u u') (wim (weq v v') (eqContext (u ∷ v ∷ 0) (u' ∷ v' ∷ 0)))) := by
  have b1 := eqContext_cons_backward (0 : V) 0 v v'
  rw [R2Quant.eqContext_nil] at b1
  have b2 := eqContext_cons_backward (v ∷ (0 : V)) (v' ∷ 0) u u'
  have t1 : CProv (wim (weq v v') (eqContext (v ∷ (0 : V)) (v' ∷ 0))) :=
    compose (conj_under (self_imp _) (cProv_mp (cProv_k 0 (weq v v')) cProv_truth)) b1
  exact ded2 (.mp (.ax b2) (.mp (.mp (.ax (conj_intro_imp _ _)) h1) (.mp (.ax t1) h0)))

/-! ## Matrix Leibniz at a fixed odd stream -/

section Matrix

variable [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 2]

/-- The matrix with its two slots labelled `u`, `v`, at stream `w`. -/
abbrev Mx (F w : V) (K : V) (u v : V) : V := encode F (u ∷ v ∷ 0) w K

lemma streamEnv_two_big {s u v : V} (hu : u < s) (hv : v < s) : StreamEnv s (u ∷ v ∷ 0) :=
  fun k ↦ avoid_cons (avoid_cons (avoid_nil _)
    (ne_of_gt (lt_of_lt_of_le hv (le_add_of_nonneg_right (Arithmetic.zero_le _)))))
    (ne_of_gt (lt_of_lt_of_le hu (le_add_of_nonneg_right (Arithmetic.zero_le _))))

lemma streamEnv_two_parity {s u v : V} (hs : s % 2 = 0) (hu : u % 2 = 1) (hv : v % 2 = 1) :
    StreamEnv s (u ∷ v ∷ 0) :=
  fun k ↦ avoid_cons (avoid_cons (avoid_nil _) (ne_of_parity (even_add_two_mul hs k) hv))
    (ne_of_parity (even_add_two_mul hs k) hu)

/-- **Matrix Leibniz**: at a common odd stream above everything, equal slot labels
give equivalent matrices. -/
theorem mx_leibniz {K F w u v u' v' : V} (hK : IsSemiformula ℒₛₑₜ 2 K) (hF : OddEnv F)
    (hw : w % 2 = 1) (hFw : F < w) (h1w : 1 < w)
    (hu : u % 2 = 1) (hv : v % 2 = 1) (hu' : u' % 2 = 1) (hv' : v' % 2 = 1)
    (huw : u < w) (hvw : v < w) (hu'w : u' < w) (hv'w : v' < w) :
    CProv (wim (eqContext (u ∷ v ∷ 0) (u' ∷ v' ∷ 0)) (wim (Mx F w K u v) (Mx F w K u' v'))) := by
  have h2 : (2 : V) % 2 = 0 := by simp
  have f1 : FreshPair F (u ∷ v ∷ 0) (u' ∷ v' ∷ 0) w 2 :=
    ⟨streamFree_big hFw h1w, streamFree_even h2 hF, streamEnv_two_big huw hvw,
      streamEnv_two_big hu'w hv'w, streamEnv_two_parity h2 hu hv, streamEnv_two_parity h2 hu' hv',
      apart_of_mod_ne (by rw [hw, h2]; simp)⟩
  have f2 : FreshPair F (u' ∷ v' ∷ 0) (u' ∷ v' ∷ 0) 2 w :=
    ⟨streamFree_even h2 hF, streamFree_big hFw h1w, streamEnv_two_parity h2 hu' hv',
      streamEnv_two_parity h2 hu' hv', streamEnv_two_big hu'w hv'w, streamEnv_two_big hu'w hv'w,
      apart_of_mod_ne (by rw [hw, h2]; simp)⟩
  have e1 := encode_eq_under hK F _ _ w 2 (by simp [one_add_one_eq_two])
    (by simp [one_add_one_eq_two]) f1
  have e2 := encode_eq_under hK F _ _ 2 w (by simp [one_add_one_eq_two])
    (by simp [one_add_one_eq_two]) f2
  have hc : CProv (eqContext (u' ∷ v' ∷ (0 : V)) (u' ∷ v' ∷ 0)) :=
    cProv_mp (cProv_mp (ctx2_intro u' v' u' v') (eq_refl u')) (eq_refl v')
  exact ded2 (.mp (.mp (.ax e2.1) (.ax hc)) (.mp (.mp (.ax e1.1) h1) h0))

end Matrix


/-! ## Atoms between bound slots -/

/-- A membership atom between two bound slots encodes to `wel` of their labels. -/
lemma encode_mem_bvars {n : ℕ} (F B s : V) (i j : Fin n) :
    encode F B s (Bootstrapping.Semiformula.rel (Language.Mem.mem : (ℒₛₑₜ).Rel 2)
      ![Bootstrapping.Semiterm.bvar i, Bootstrapping.Semiterm.bvar j]).val =
      wel B.[(i : V)] B.[(j : V)] := by
  have hu := (Bootstrapping.Semiformula.rel (Language.Mem.mem : (ℒₛₑₜ).Rel 2)
    ![Bootstrapping.Semiterm.bvar (V := V) i, Bootstrapping.Semiterm.bvar j]).isSemiformula.isUFormula
  rw [Bootstrapping.Semiformula.rel_val] at hu
  rw [Bootstrapping.Semiformula.rel_val,
    encode_rel F B s (IsUFormula.rel.mp hu).1 (IsUFormula.rel.mp hu).2]
  have hv := (IsUFormula.rel.mp hu).2
  have h0 := TermLabels.vec_nth F B hv (show (0 : V) < ↑(2 : ℕ) by simp)
  have h1 := TermLabels.vec_nth F B hv (show (1 : V) < ↑(2 : ℕ) by simp [one_lt_two])
  simp only [Formulas.atom, nth_adjoin_zero, nth_adjoin_one, nth_adjoin_two]
  rw [if_neg (by change ((1 : ℕ) : V) ≠ 0; simp), h0, h1]
  simp [Matrix.vecHead, Matrix.vecTail]

lemma quote_bvar2 {n : ℕ} (i j : Fin n) :
    (fun k ↦ (⌜(![#i, #j] : Fin 2 → SyntacticSemiterm ℒₛₑₜ n) k⌝ : Bootstrapping.Semiterm V ℒₛₑₜ n)) =
      ![Bootstrapping.Semiterm.bvar i, Bootstrapping.Semiterm.bvar j] :=
  funext fun k ↦ by match k with | 0 => simp | 1 => simp

lemma enc_YB3 (F B s : V) : encode F B s (⌜gicAtomYB3⌝ : SF (V := V) 3).val = wel B.[0] B.[1] := by
  rw [gicAtomYB3, FirstOrder.Semiformula.typed_quote_rel, quote_bvar2, encode_mem_bvars]; simp
lemma enc_XA3 (F B s : V) : encode F B s (⌜gicAtomXA3⌝ : SF (V := V) 3).val = wel B.[0] B.[2] := by
  rw [gicAtomXA3, FirstOrder.Semiformula.typed_quote_rel, quote_bvar2, encode_mem_bvars]; simp
lemma enc_YB4 (F B s : V) : encode F B s (⌜gicAtomYB4⌝ : SF (V := V) 4).val = wel B.[0] B.[2] := by
  rw [gicAtomYB4, FirstOrder.Semiformula.typed_quote_rel, quote_bvar2, encode_mem_bvars]; simp

lemma enc_neg_atom {n : ℕ} (F B s : V) (A : SF (V := V) n) (a : V)
    (h : encode F B s A.val = a) (hA : ∃ R v, A = Bootstrapping.Semiformula.rel (L := ℒₛₑₜ) (k := 2) R v) :
    encode F B s (neg ℒₛₑₜ A.val) = wim a 1 := by
  obtain ⟨R, v, rfl⟩ := hA
  have hu := (Bootstrapping.Semiformula.rel R v).isSemiformula.isUFormula
  rw [Bootstrapping.Semiformula.rel_val] at hu h ⊢
  rw [neg_rel (IsUFormula.rel.mp hu).1 (IsUFormula.rel.mp hu).2,
    encode_nrel F B s (IsUFormula.rel.mp hu).1 (IsUFormula.rel.mp hu).2,
    ← encode_rel F B s (IsUFormula.rel.mp hu).1 (IsUFormula.rel.mp hu).2, h]

/-- Substituting two bound variables into the matrix moves their labels into its stack. -/
lemma enc_subst2 {n : ℕ} (F B s : V) (K : SF (V := V) 2) (i j : Fin n) :
    encode F B s (K.subst ![Bootstrapping.Semiterm.bvar i, Bootstrapping.Semiterm.bvar j]).val =
      encode F (B.[(i : V)] ∷ B.[(j : V)] ∷ 0) s K.val := by
  rw [Bootstrapping.Semiformula.val_substs]
  have h := encode_subst_pair K.isSemiformula (Bootstrapping.Semiterm.bvar (V := V) (L := ℒₛₑₜ) i).isSemiterm
    (Bootstrapping.Semiterm.bvar (V := V) (L := ℒₛₑₜ) j).isSemiterm F B s
  simp only [Bootstrapping.Semiterm.bvar_val, TermLabels.term_bvar] at h
  convert h using 2
  simp [Bootstrapping.SemitermVec.val, Matrix.vecHead, Matrix.vecTail]

lemma nth_two_cons (a b c d : V) : (a ∷ b ∷ c ∷ d).[2] = c := by
  rw [← one_add_one_eq_two, nth_adjoin_succ, nth_adjoin_one, nth_adjoin_zero]

/-- The support clause of the encoded GIC body. -/
noncomputable def SUPc (F t k : V) : V :=
  wal (t + 2 + 2) (wim (neg (neg (wel (t + 2 + 2) (t + 2))))
    (ex (t + 2 + 2 + 2) (encode F ((t + 2 + 2 + 2) ∷ (t + 2 + 2) ∷ 0) (t + 2 + 2 + 2 + 2) k)))

/-- The coverage clause of the encoded GIC body. -/
noncomputable def COVc (F t k : V) : V :=
  wal (t + 2 + 2) (wim (neg (neg (wel (t + 2 + 2) t)))
    (wim (neg (wal (t + 2 + 2 + 2)
        (encode F ((t + 2 + 2) ∷ (t + 2 + 2 + 2) ∷ 0) (t + 2 + 2 + 2 + 2) (Bootstrapping.neg ℒₛₑₜ k))))
      (ex (t + 2 + 2 + 2) (conj (wel (t + 2 + 2 + 2) (t + 2))
        (encode F ((t + 2 + 2) ∷ (t + 2 + 2 + 2) ∷ 0) (t + 2 + 2 + 2 + 2) k)))))

/-- **The encoded GIC body.** -/
theorem encode_gicBody (K : SF (V := V) 2) (F t : V) :
    encode F 0 t (gicBody K).val = wal t (ex (t + 2) (conj (SUPc F t K.val) (COVc F t K.val))) := by
  have hq : ∀ {n : ℕ} (i : Fin n),
      (⌜(#i : SyntacticSemiterm ℒₛₑₜ n)⌝ : Bootstrapping.Semiterm V ℒₛₑₜ n) =
        Bootstrapping.Semiterm.bvar i := fun i ↦ by simp
  have hneg : ∀ {n : ℕ} (B s : V) (X : SF (V := V) (n + 1)),
      encode F B s (Bootstrapping.neg ℒₛₑₜ (∃⁰ X).val) =
        wal s (encode F (s ∷ B) (s + 2) (Bootstrapping.neg ℒₛₑₜ X.val)) := by
    intro n B s X
    rw [← Bootstrapping.Semiformula.val_neg, Bootstrapping.Semiformula.neg_ex, encT_all,
      Bootstrapping.Semiformula.val_neg]
  simp only [gicBody, encT_all, encT_exs, encT_and, encT_imp, enc_YB4, hq, enc_subst2, hneg]
  rw [enc_neg_atom _ _ _ _ _ (enc_YB3 _ _ _) ⟨_, _, by rw [gicAtomYB3, FirstOrder.Semiformula.typed_quote_rel]⟩,
    enc_neg_atom _ _ _ _ _ (enc_XA3 _ _ _) ⟨_, _, by rw [gicAtomXA3, FirstOrder.Semiformula.typed_quote_rel]⟩]
  rw [← Bootstrapping.Semiformula.val_neg, ← Bootstrapping.Semiformula.substs_neg, enc_subst2,
    Bootstrapping.Semiformula.val_neg]
  simp only [Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one, nth_adjoin_zero,
    nth_adjoin_one, nth_two_cons, SUPc, COVc]





/-! ## Reasoning under a vacuous hypothesis -/

lemma vac_conj {i a b : V} (va : Vac i a) (vb : Vac i b) : Vac i (conj a b) :=
  vac_neg (vac_imp va (vac_neg vb))

lemma vac_ex (j : V) {i p : V} (v : Vac i p) : Vac i (ex j p) :=
  vac_neg (vac_all j (vac_neg v))

lemma all_under {h x A B : V} (vh : Vac x h) (H : CProv (wim h (wim A B))) :
    CProv (wim h (wim (wal x A) (wal x B))) :=
  compose (compose vh (all_mono x H)) (all_distribution x A B)

lemma ex_under {h x A B : V} (vh : Vac x h) (H : CProv (wim h (wim A B))) :
    CProv (wim h (wim (ex x A) (ex x B))) :=
  compose (compose vh (all_mono x H)) (all_imp_ex x A B)

lemma imp_under {h A A' B B' : V} (HA : CProv (wim h (wim A' A))) (HB : CProv (wim h (wim B B'))) :
    CProv (wim h (wim (wim A B) (wim A' B'))) :=
  ValidatorImplicationContext.imp_under CProv cProv_classical HA HB

lemma conj_under' {h A A' B B' : V} (HA : CProv (wim h (wim A A'))) (HB : CProv (wim h (wim B B'))) :
    CProv (wim h (wim (conj A B) (conj A' B'))) := by
  have t1 : CProv (wim h (wim (conj A B) A')) :=
    ded2 (.mp (.mp (.ax HA) h1) (.mp (.ax (conj_left A B)) h0))
  have t2 : CProv (wim h (wim (conj A B) B')) :=
    ded2 (.mp (.mp (.ax HB) h1) (.mp (.ax (conj_right A B)) h0))
  exact ded2 (.mp (.mp (.ax (conj_intro_imp A' B')) (.mp (.mp (.ax t1) h1) h0))
    (.mp (.mp (.ax t2) h1) h0))

lemma all_rename_ctx {h x y A B : V} (hL : CProv (wim h (wim (weq x y) (wim A B))))
    (vxh : Vac x h) (vyh : Vac y h) (vxB : Vac x B) (vy : Vac y (wal x A)) :
    CProv (wim h (wim (wal x A) (wal y B))) :=
  all_relational h A B x y hL vxh vxB vyh vy

lemma ex_rename_ctx {h x y A B : V} (hL : CProv (wim h (wim (weq x y) (wim A B))))
    (vxh : Vac x h) (vyh : Vac y h) (vyA : Vac y A) (vx : Vac x (ex y B)) :
    CProv (wim h (wim (ex x A) (ex y B))) := by
  have s0 : CProv (wim h (wim A (wim (weq y x) B))) :=
    ded3 (.mp (.mp (.mp (.ax hL) h2) (.mp (.ax (eq_symm y x)) h0)) h1)
  have s1 := all_under_two y s0 vyh vyA
  have s2 : CProv (wim (wal y (wim (weq y x) B)) (ex y B)) :=
    ded1 (.mp (.mp (.ax (all_imp_ex y (weq y x) B)) h0) (.ax (ex_equality y x)))
  have s3 : CProv (wim h (wim A (ex y B))) := ded2 (.mp (.ax s2) (.mp (.mp (.ax s1) h1) h0))
  exact ded2 (.mp (.ax (ex_elim_of_vac vx)) (.mp (.mp (.ax (ex_under vxh s3)) h1) h0))

/-- A theorem holds under any hypothesis. -/
lemma under {h A : V} (H : CProv A) : CProv (wim h A) := cProv_mp (cProv_k A h) H

/-! ## The bridge from the literal native GIC instance -/

lemma odd_add_two {x : V} (h : x % 2 = 1) : (x + 2) % 2 = 1 := by
  rw [show x + 2 = x + 2 * 1 by simp]; exact odd_add_two_mul h 1

lemma conj_swap (A B : V) : CProv (wim (conj A B) (conj B A)) :=
  ded1 (.mp (.mp (.ax (conj_intro_imp B A)) (.mp (.ax (conj_right A B)) h0))
    (.mp (.ax (conj_left A B)) h0))

/-- Under `h`, implications pass through double negation. -/
lemma dneg_under {h X Y : V} (H : CProv (wim h (wim X Y))) :
    CProv (wim h (wim (neg (neg X)) (neg (neg Y)))) :=
  contra_under (contra_under H)

/-- The support clause with abstract labels. -/
noncomputable def SUPg (F t2 t4 t6 t8 k : V) : V :=
  wal t4 (wim (neg (neg (wel t4 t2))) (ex t6 (encode F (t6 ∷ t4 ∷ 0) t8 k)))

/-- The coverage clause with abstract labels and domain `d`. -/
noncomputable def COVg (F d t2 t4 t6 t8 k : V) : V :=
  wal t4 (wim (neg (neg (wel t4 d)))
    (wim (neg (wal t6 (encode F (t4 ∷ t6 ∷ 0) t8 (Bootstrapping.neg ℒₛₑₜ k))))
      (ex t6 (conj (wel t6 t2) (encode F (t4 ∷ t6 ∷ 0) t8 k)))))

lemma SUPc_eq (F t k : V) : SUPc F t k = SUPg F (t + 2) (t + 2 + 2) (t + 2 + 2 + 2) (t + 2 + 2 + 2 + 2) k := rfl
lemma COVc_eq (F t k : V) :
    COVc F t k = COVg F t (t + 2) (t + 2 + 2) (t + 2 + 2 + 2) (t + 2 + 2 + 2 + 2) k := rfl

section Bridge

variable [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 2]

/-- **The native GIC bridge**, at abstract odd labels `F < a < b < t < t2 < t4 < t6 < t8`. -/
theorem gic_bridge_core (K : SF (V := V) 2) {F a b t t2 t4 t6 t8 : V} (hF : OddEnv F)
    (oa : a % 2 = 1) (ob : b % 2 = 1) (ot : t % 2 = 1) (ot2 : t2 % 2 = 1) (ot4 : t4 % 2 = 1)
    (ot6 : t6 % 2 = 1) (ot8 : t8 % 2 = 1)
    (lFa : F < a) (l1a : 1 < a) (lab : a < b) (lbt : b < t) (ltt2 : t < t2) (lt24 : t2 < t4)
    (lt46 : t4 < t6) (lt68 : t6 < t8) :
    CProv (wal t (ex t2 (conj (SUPg F t2 t4 t6 t8 K.val) (COVg F t t2 t4 t6 t8 K.val)))) := by
  have hK : IsSemiformula ℒₛₑₜ 2 K.val := K.isSemiformula
  have hKn : IsSemiformula ℒₛₑₜ 2 (Bootstrapping.neg ℒₛₑₜ K.val) := (∼K).isSemiformula
  have lFb := lFa.trans lab
  have lFt := lFb.trans lbt
  have lFt2 := lFt.trans ltt2
  have lFt4 := lFt2.trans lt24
  have lFt6 := lFt4.trans lt46
  have lFt8 := lFt6.trans lt68
  have l1b := l1a.trans lab
  have l1t := l1b.trans lbt
  have l1t2 := l1t.trans ltt2
  have l1t4 := l1t2.trans lt24
  have l1t6 := l1t4.trans lt46
  have l1t8 := l1t6.trans lt68
  have lat := lab.trans lbt
  have lbt2 := lbt.trans ltt2
  have lbt4 := lbt2.trans lt24
  have lbt6 := lbt4.trans lt46
  have lbt8 := lbt6.trans lt68
  have lat2 := lat.trans ltt2
  have lat4 := lat2.trans lt24
  have lat6 := lat4.trans lt46
  have lat8 := lat6.trans lt68
  have ltt4 := ltt2.trans lt24
  have ltt6 := ltt4.trans lt46
  have ltt8 := ltt6.trans lt68
  have lt26 := lt24.trans lt46
  have lt28 := lt26.trans lt68
  have lt48 := lt46.trans lt68
  have vP : ∀ {k z u v : V}, IsSemiformula ℒₛₑₜ 2 k → FreeAvoid z F → z ≠ u → z ≠ v →
      StreamAvoid z t8 → Vac z (encode F (u ∷ v ∷ 0) t8 k) := by
    intro k z u v hk hzF hzu hzv hzs
    exact encode_vac hk F (u ∷ v ∷ 0) t8 _ (by simp [one_add_one_eq_two]) hzF
      (avoid_cons (avoid_cons (avoid_nil _) hzv) hzu) hzs
  have mxL : ∀ {k u v u' v' : V}, IsSemiformula ℒₛₑₜ 2 k → u % 2 = 1 → v % 2 = 1 →
      u' % 2 = 1 → v' % 2 = 1 → u < t8 → v < t8 → u' < t8 → v' < t8 →
      CProv (wim (weq u u') (wim (weq v v')
        (wim (encode F (u ∷ v ∷ 0) t8 k) (encode F (u' ∷ v' ∷ 0) t8 k)))) := by
    intro k u v u' v' hk hu hv hu' hv' g1 g2 g3 g4
    have m := mx_leibniz hk hF ot8 lFt8 l1t8 hu hv hu' hv' g1 g2 g3 g4
    exact ded3 (.mp (.mp (.ax m) (.mp (.mp (.ax (ctx2_intro u v u' v')) h2) h1)) h0)
  -- the literal instance
  have ec : pad (encode F (a ∷ b ∷ 0) t8 K.val) % 2 = 0 := pad_even _
  generalize hc : pad (encode F (a ∷ b ∷ 0) t8 K.val) = c at ec
  have hLit : CProv (internalGic a b c (encode F (a ∷ b ∷ 0) t8 K.val)) := by
    rw [← hc]
    exact cProv_mp (ValidatorNativeGicCongruence254.internalGic_pad_equivalent a b _).2
      (cProv_internalGic a b _ (hc ▸ ne_of_parity ec oa) (hc ▸ ne_of_parity ec ob))
  -- abbreviations
  set Pab := encode F (a ∷ b ∷ 0) t8 K.val with hPab
  have hca : c ≠ a := ne_of_parity ec oa
  have hcb : c ≠ b := ne_of_parity ec ob
  have hct2 : c ≠ t2 := ne_of_parity ec ot2
  have vcP : Vac c Pab := vP hK (freeAvoid_even ec hF) hca hcb (streamAvoid_parity' ec ot8)
  have self : ∀ h X : V, CProv (wim h (wim X X)) := fun h X ↦ under (self_imp X)
  -- Stage 1: rename the collection label c to t2
  have S1 : CProv (wim (internalGic a b c Pab)
      (ex t2 (conj (wal a (wim (wel a b) (wal b (wim Pab (ex b (conj Pab (wel b t2)))))))
        (wal b (wim (wel b t2) (ex a Pab)))))) := by
    have vah : Vac a (weq c t2) := vac_eq c t2 a hca.symm lat2.ne
    have vbh : Vac b (weq c t2) := vac_eq c t2 b hcb.symm lbt2.ne
    have Hr : CProv (wim (weq c t2) (wim (wel b c) (wel b t2))) := rel_right c t2 b
    have Hr' : CProv (wim (weq c t2) (wim (wel b t2) (wel b c))) :=
      ded2 (.mp (.mp (.ax (rel_right t2 c b)) (.mp (.ax (eq_symm c t2)) h1)) h0)
    have H1 := all_under vah (imp_under (self _ (wel a b)) (all_under vbh
      (imp_under (self _ Pab) (ex_under vbh (conj_under' (self _ Pab) Hr)))))
    have H2 := all_under vbh (imp_under Hr' (self _ (ex a Pab)))
    have vt2P : Vac t2 Pab := vP hK (freeAvoid_big lFt2 l1t2) lat2.ne' lbt2.ne' (streamAvoid_big lt28)
    have vyA : Vac t2 (conj (wal a (wim (wel a b) (wal b (wim Pab (ex b (conj Pab (wel b c)))))))
        (wal b (wim (wel b c) (ex a Pab)))) :=
      vac_conj (vac_all a (vac_imp (vac_rel a b t2 lat2.ne' lbt2.ne') (vac_all b (vac_imp vt2P
        (vac_ex b (vac_conj vt2P (vac_rel b c t2 lbt2.ne' hct2.symm)))))))
        (vac_all b (vac_imp (vac_rel b c t2 lbt2.ne' hct2.symm) (vac_ex a vt2P)))
    have vx := vac_ex t2 (vac_conj (vac_all a (vac_imp (vac_rel a b c hca hcb) (vac_all b (vac_imp vcP
        (vac_ex b (vac_conj vcP (vac_rel b t2 c hcb hct2)))))))
        (vac_all b (vac_imp (vac_rel b t2 c hcb hct2) (vac_ex a vcP))))
    exact ex_rename (conj_under' H1 H2) vyA vx
  -- Stage 2: swap the clauses
  have S2 := ex_mono t2 (conj_swap (wal a (wim (wel a b) (wal b (wim Pab (ex b (conj Pab (wel b t2)))))))
    (wal b (wim (wel b t2) (ex a Pab))))
  -- Stage 3a: the support clause
  have S3a : CProv (wim (wal b (wim (wel b t2) (ex a Pab))) (SUPg F t2 t4 t6 t8 K.val)) := by
    unfold SUPg
    set Q := encode F (t6 ∷ t4 ∷ 0) t8 K.val
    have HA : CProv (wim (weq b t4) (wim (neg (neg (wel t4 t2))) (wel b t2))) :=
      ded2 (.mp (.mp (.ax (rel_left t4 b t2)) (.mp (.ax (eq_symm b t4)) h1))
        (.mp (.ax (double_neg_elim _)) h0))
    have m := mxL hK oa ob ot6 ot4 lat8 lbt8 lt68 lt48
    have hL1 : CProv (wim (weq b t4) (wim (weq a t6) (wim Pab Q))) :=
      ded3 (.mp (.mp (.mp (.ax m) h1) h2) h0)
    have HB := ex_rename_ctx hL1 (vac_eq b t4 a lab.ne lat4.ne) (vac_eq b t4 t6 lbt6.ne' lt46.ne')
      (vP hK (freeAvoid_big lFt6 l1t6) lat6.ne' lbt6.ne' (streamAvoid_big lt68))
      (vac_ex t6 (vP hK (freeAvoid_big lFa l1a) lat6.ne lat4.ne (streamAvoid_big lat8)))
    exact all_rename (imp_under HA HB)
      (vac_imp (vac_neg (vac_neg (vac_rel t4 t2 b lbt4.ne lbt2.ne)))
        (vac_ex t6 (vP hK (freeAvoid_big lFb l1b) lbt6.ne lbt4.ne (streamAvoid_big lbt8))))
      (vac_all b (vac_imp (vac_rel b t2 t4 lbt4.ne' lt24.ne')
        (vac_ex a (vP hK (freeAvoid_big lFt4 l1t4) lat4.ne' lbt4.ne' (streamAvoid_big lt48)))))
  -- Stage 3b: the coverage clause
  have S3b : CProv (wim (wal a (wim (wel a b) (wal b (wim Pab (ex b (conj Pab (wel b t2)))))))
      (COVg F b t2 t4 t6 t8 K.val)) := by
    unfold COVg
    set E : V → V := fun u ↦ ex t6 (conj (wel t6 t2) (encode F (u ∷ t6 ∷ 0) t8 K.val))
    set Pat6 := encode F (a ∷ t6 ∷ 0) t8 K.val
    set Pnat6 := encode F (a ∷ t6 ∷ 0) t8 (Bootstrapping.neg ℒₛₑₜ K.val)
    have vt6P : Vac t6 Pab := vP hK (freeAvoid_big lFt6 l1t6) lat6.ne' lbt6.ne' (streamAvoid_big lt68)
    have vbPat6 : Vac b Pat6 := vP hK (freeAvoid_big lFb l1b) lab.ne' lbt6.ne (streamAvoid_big lbt8)
    have vbE : Vac b (E a) := vac_ex t6 (vac_conj (vac_rel t6 t2 b lbt6.ne lbt2.ne) vbPat6)
    have i1 : CProv (wim (ex b (conj Pab (wel b t2))) (E a)) := by
      have m := mxL hK oa ob oa ot6 lat8 lbt8 lat8 lt68
      have mL : CProv (wim (weq b t6) (wim Pab Pat6)) :=
        ded2 (.mp (.mp (.mp (.ax m) (.ax (eq_refl a))) h1) h0)
      have hL2 : CProv (wim (weq b t6) (wim (conj Pab (wel b t2)) (conj (wel t6 t2) Pat6))) :=
        ded2 (.mp (.ax (conj_swap _ _)) (.mp (.mp (.ax (conj_under' mL (rel_left b t6 t2))) h1) h0))
      exact ex_rename hL2 (vac_conj vt6P (vac_rel b t2 t6 lbt6.ne' lt26.ne')) vbE
    have i2 := all_mono b (ValidatorNativeGicCongruence254.cProv_imp_mono (self_imp Pab) i1)
    have i3 : CProv (wim (wal b (wim Pab (E a))) (wim (ex b Pab) (E a))) :=
      ded2 (.mp (.ax (ex_elim_of_vac vbE)) (.mp (.mp (.ax (all_imp_ex b Pab (E a))) h1) h0))
    have ne := encode_neg hK F (a ∷ t6 ∷ 0) t8
    have n1 : CProv (wim (neg (wal t6 Pnat6)) (ex t6 Pat6)) := contrapose_of (all_mono t6 ne.2)
    have n2 : CProv (wim (ex t6 Pat6) (ex b Pab)) := by
      have m := mxL hK oa ot6 oa ob lat8 lt68 lat8 lbt8
      have hL3 : CProv (wim (weq t6 b) (wim Pat6 Pab)) :=
        ded2 (.mp (.mp (.mp (.ax m) (.ax (eq_refl a))) h1) h0)
      exact ex_rename hL3 vbPat6 (vac_ex b vt6P)
    have stepY : CProv (wim (wal b (wim Pab (ex b (conj Pab (wel b t2)))))
        (wim (neg (wal t6 Pnat6)) (E a))) :=
      compose (compose i2 i3)
        (ValidatorNativeGicCongruence254.cProv_imp_mono (compose n1 n2) (self_imp (E a)))
    have ii := all_mono a (ValidatorNativeGicCongruence254.cProv_imp_mono (self_imp (wel a b)) stepY)
    have vt6h : Vac t6 (weq a t4) := vac_eq a t4 t6 lat6.ne' lt46.ne'
    have HA3 : CProv (wim (weq a t4) (wim (neg (neg (wel t4 b))) (wel a b))) :=
      ded2 (.mp (.mp (.ax (rel_left t4 a b)) (.mp (.ax (eq_symm a t4)) h1))
        (.mp (.ax (double_neg_elim _)) h0))
    have mLn : CProv (wim (weq a t4)
        (wim Pnat6 (encode F (t4 ∷ t6 ∷ 0) t8 (Bootstrapping.neg ℒₛₑₜ K.val)))) := by
      have m := mxL hKn oa ot6 ot4 ot6 lat8 lt68 lt48 lt68
      exact ded2 (.mp (.mp (.mp (.ax m) h1) (.ax (eq_refl t6))) h0)
    have mL4 : CProv (wim (weq a t4) (wim Pat6 (encode F (t4 ∷ t6 ∷ 0) t8 K.val))) := by
      have m := mxL hK oa ot6 ot4 ot6 lat8 lt68 lt48 lt68
      exact ded2 (.mp (.mp (.mp (.ax m) h1) (.ax (eq_refl t6))) h0)
    have HB3 := imp_under (contra_under (all_under vt6h mLn))
      (ex_under vt6h (conj_under' (self _ (wel t6 t2)) mL4))
    have iii := all_rename (imp_under HA3 HB3)
      (vac_imp (vac_neg (vac_neg (vac_rel t4 b a lat4.ne lab.ne)))
        (vac_imp (vac_neg (vac_all t6 (vP hKn (freeAvoid_big lFa l1a) lat4.ne lat6.ne (streamAvoid_big lat8))))
          (vac_ex t6 (vac_conj (vac_rel t6 t2 a lat6.ne lat2.ne)
            (vP hK (freeAvoid_big lFa l1a) lat4.ne lat6.ne (streamAvoid_big lat8))))))
      (vac_all a (vac_imp (vac_rel a b t4 lat4.ne' lbt4.ne')
        (vac_imp (vac_neg (vac_all t6 (vP hKn (freeAvoid_big lFt4 l1t4) lat4.ne' lt46.ne (streamAvoid_big lt48))))
          (vac_ex t6 (vac_conj (vac_rel t6 t2 t4 lt46.ne lt24.ne')
            (vP hK (freeAvoid_big lFt4 l1t4) lat4.ne' lt46.ne (streamAvoid_big lt48)))))))
    exact compose ii iii
  -- Stage 4: the body with free domain b
  have Gb : CProv (ex t2 (conj (SUPg F t2 t4 t6 t8 K.val) (COVg F b t2 t4 t6 t8 K.val))) :=
    cProv_mp (ex_mono t2 (ValidatorNativeGicCongruence254.cProv_conj_mono S3a S3b))
      (cProv_mp S2 (cProv_mp S1 hLit))
  -- Stage 5: generalize the domain and rename it to t
  have vtF : FreeAvoid t F := freeAvoid_big lFt l1t
  have vbF : FreeAvoid b F := freeAvoid_big lFb l1b
  have vSUP : ∀ z : V, FreeAvoid z F → z ≠ t2 → z ≠ t4 → z ≠ t6 → z < t8 →
      Vac z (SUPg F t2 t4 t6 t8 K.val) := fun z hzF g2 g4 g6 g8 ↦
    vac_all t4 (vac_imp (vac_neg (vac_neg (vac_rel t4 t2 z g4 g2)))
      (vac_ex t6 (vP hK hzF g6 g4 (streamAvoid_big g8))))
  have vCOV : ∀ z d : V, FreeAvoid z F → z ≠ d → z ≠ t2 → z ≠ t4 → z ≠ t6 → z < t8 →
      Vac z (COVg F d t2 t4 t6 t8 K.val) := fun z d hzF gd g2 g4 g6 g8 ↦
    vac_all t4 (vac_imp (vac_neg (vac_neg (vac_rel t4 d z g4 gd)))
      (vac_imp (vac_neg (vac_all t6 (vP hKn hzF g4 g6 (streamAvoid_big g8))))
        (vac_ex t6 (vac_conj (vac_rel t6 t2 z g6 g2) (vP hK hzF g4 g6 (streamAvoid_big g8))))))
  have HA5 : CProv (wim (weq b t) (wim (neg (neg (wel t4 t))) (neg (neg (wel t4 b))))) :=
    dneg_under (ded2 (.mp (.mp (.ax (rel_right t b t4)) (.mp (.ax (eq_symm b t)) h1)) h0))
  have hL5 : CProv (wim (weq b t)
      (wim (ex t2 (conj (SUPg F t2 t4 t6 t8 K.val) (COVg F b t2 t4 t6 t8 K.val)))
        (ex t2 (conj (SUPg F t2 t4 t6 t8 K.val) (COVg F t t2 t4 t6 t8 K.val))))) := by
    unfold COVg
    exact ex_under (vac_eq b t t2 lbt2.ne' ltt2.ne') (conj_under' (self _ _)
      (all_under (vac_eq b t t4 lbt4.ne' ltt4.ne') (imp_under HA5 (self _ _))))
  exact cProv_mp (all_rename hL5
      (vac_ex t2 (vac_conj (vSUP b vbF lbt2.ne lbt4.ne lbt6.ne lbt8)
        (vCOV b t vbF lbt.ne lbt2.ne lbt4.ne lbt6.ne lbt8)))
      (vac_all b (vac_ex t2 (vac_conj (vSUP t vtF ltt2.ne ltt4.ne ltt6.ne ltt8)
        (vCOV t b vtF lbt.ne' ltt2.ne ltt4.ne ltt6.ne ltt8)))))
    (cProv_gen b Gb)

end Bridge


end LeanProofs.ZFCinPA.R2Gic
