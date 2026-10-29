import ZFCinPA.SizedCongruenceAtoms

/-!
# The placeholder congruence leaves, bounded

A template derivation may use the equality axioms of the enlarged language;
for a placeholder of arity `a` such an axiom translates to
`SetCongruence.congruenceFormula a K`:

  `∀ x₀ … x_{a-1} y₀ … y_{a-1}, ⋀ⱼ xⱼ = yⱼ → K(x) → K(y)`.

This module derives it with an explicit bound for every internal `K`, from
`SizedCongruenceAtoms.replace_le`:

* `strip` removes the `2a` universal binders (each costs a weakening and a
  `∀` rule), leaving the body at the free variables `&0 … &(2a-1)`;
* `unpack` takes the conjunction context apart into its negated atoms;
* `symcut` supplies the reversed hypotheses `yⱼ ≠ xⱼ` that `replace_le`
  needs, by a bounded symmetry theorem.
-/
set_option autoImplicit false
noncomputable section

namespace LeanProofs.ZFCinPA.SizedPlaceholderCongruence

open LO LO.FirstOrder LO.FirstOrder.SetTheory LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic
open LeanProofs.BoundedPAConsistency.SizedDerivation
open LeanProofs.ZFCinPA.SetCodeLevels LeanProofs.ZFCinPA.LevelDerivation
open LeanProofs.ZFCinPA.SizedCongruence LeanProofs.ZFCinPA.SizedCongruenceAtoms

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Iterated shifts and the free-variable vector -/

/-- `k`-fold shift. -/
def shs {n : ℕ} (k : ℕ) (φ : Bootstrapping.Semiformula V ℒₛₑₜ n) :
    Bootstrapping.Semiformula V ℒₛₑₜ n :=
  (Bootstrapping.Semiformula.shift)^[k] φ

theorem shs_succ {n : ℕ} (k : ℕ) (φ : Bootstrapping.Semiformula V ℒₛₑₜ n) :
    shs (k + 1) φ = (shs k φ).shift :=
  Function.iterate_succ_apply' _ _ _

theorem shs_all {n : ℕ} (φ : Bootstrapping.Semiformula V ℒₛₑₜ (n + 1)) :
    ∀ k : ℕ, shs k (∀⁰ φ) = ∀⁰ (shs k φ)
  | 0 => rfl
  | k + 1 => by rw [shs_succ, shs_succ, shs_all φ k, Bootstrapping.Semiformula.shift_all]

theorem shs_level {n : ℕ} (φ : Bootstrapping.Semiformula V ℒₛₑₜ n) {u : V}
    (h : φ.val ≤ lvB u) : ∀ k : ℕ, (shs k φ).val ≤ lvB (u + k)
  | 0 => by simpa [shs] using h
  | k + 1 => by
      rw [shs_succ, Bootstrapping.Semiformula.val_shift]
      have := shift_level (shs_level φ h k)
      push_cast
      rwa [← add_assoc]

/-- The vector `&0, …, &(n-1)`. -/
def fvVec (n : ℕ) : Bootstrapping.SemitermVec V ℒₛₑₜ n 0 :=
  fun j => Bootstrapping.Semiterm.fvar ((j : ℕ) : V)

theorem fvar_small : ∀ j : ℕ, j ≤ 6 → (^&(j : V) : V) ≤ lvB 3
  | 0, _ => by rw [lvB_three]; simp [qqFvar, pair]; norm_num
  | 1, _ => by rw [lvB_three]; simp [qqFvar, pair]; norm_num
  | 2, _ => by rw [lvB_three]; simp [qqFvar, pair]; norm_num
  | 3, _ => by rw [lvB_three]; simp [qqFvar, pair]; norm_num
  | 4, _ => by rw [lvB_three]; simp [qqFvar, pair]; norm_num
  | 5, _ => by rw [lvB_three]; simp [qqFvar, pair]; norm_num
  | 6, _ => by rw [lvB_three]; simp [qqFvar, pair]; norm_num
  | j + 7, h => absurd h (by omega)

theorem fvVec_le {n : ℕ} (hn : n ≤ 6) : ∀ j, ((fvVec (V := V) n) j).val ≤ lvB 3 := fun j => by
  simpa [fvVec] using fvar_small j (by omega)

theorem free_fvVec {n : ℕ} (ψ : Bootstrapping.Semiformula V ℒₛₑₜ (n + 1)) :
    ((shs n ψ).subst (fvVec n).q).free = (shs (n + 1) ψ).subst (fvVec (n + 1)) := by
  unfold Bootstrapping.Semiformula.free
  rw [Bootstrapping.Semiformula.shift_substs, Bootstrapping.Semiformula.substs_substs, shs_succ]
  congr 1
  funext j
  cases j using Fin.cases with
  | zero => simp [fvVec]
  | succ j => simp [fvVec, Function.comp_def]

/-! ## Stripping universal binders -/

/-- The member level of the binder-stripping step. -/
def sβ (x : V) : V := 10 * (x + 3) + 3

theorem lt_lvB_of {x m W : V} (hx : x ≤ lvB m) (hW : m + 1 ≤ W) : x < lvB W :=
  lt_of_lt_of_le (lt_lvB_succ hx) (lvB_mono hW)

/-- One binder: `{free χ}` gives `{∀ χ}` two levels up. -/
theorem all_step {χ : Bootstrapping.Semiformula V ℒₛₑₜ 1} {W m : V} (hW4 : 4 ≤ W)
    (hA : (∀⁰ χ).val ≤ lvB m) (hF : χ.free.val ≤ lvB (m + 1)) (hmW : m + 1 + 1 ≤ W)
    (h : DLv 𝗭𝗙 (insert χ.free.val ∅) W) : DLv 𝗭𝗙 (insert (∀⁰ χ).val ∅) (W + 1 + 1) := by
  have hall : (∀⁰ χ).val = ^∀ χ.val := by simp
  have hS : setShift ℒₛₑₜ (insert (∀⁰ χ).val (∅ : V)) = insert (shift ℒₛₑₜ (∀⁰ χ).val) ∅ := by
    rw [mem_setShift_insert]
    congr 1
    exact mem_ext fun y => by simp [mem_setShift_iff]
  have hshl : shift ℒₛₑₜ (∀⁰ χ).val ≤ lvB (m + 1) := shift_level hA
  have d1 : DLv 𝗭𝗙 (insert (free ℒₛₑₜ χ.val) (setShift ℒₛₑₜ (insert (∀⁰ χ).val ∅))) (W + 1) := by
    rw [hS, ← Bootstrapping.Semiformula.free_val]
    refine DLv.wk hW4 (((SeqLt.empty W).insert (lt_lvB_of hshl hmW)).insert (lt_lvB_of hF hmW))
      ?_ (insert_subset_insert_of_subset _ (by intro z hz; simp at hz)) h
    have := (∀⁰ χ).shift.isSemiformula
    simp only [Bootstrapping.Semiformula.val_shift] at this
    simp [χ.free.isSemiformula, this]
  refine DLv.all_m (le_trans hW4 le_self_add)
    ((SeqLt.empty _).insert (lt_lvB_of hA (le_trans le_self_add (le_trans hmW le_self_add))))
    (p := χ.val) (by simp) d1

theorem strip : ∀ (n : ℕ) (φ : Bootstrapping.Semiformula V ℒₛₑₜ n) (u W : V), n ≤ 6 → 2 ≤ u →
    φ.val ≤ lvB u → 4 ≤ W → sβ (u + 3 * n) + 1 ≤ W →
    DLv 𝗭𝗙 (insert ((shs n φ).subst (fvVec n)).val ∅) W →
    DLv 𝗭𝗙 (insert (∀⁰* φ).val ∅) (W + 2 * n)
  | 0, φ, u, W, _, _, _, _, _, h => by
      simpa [shs, Bootstrapping.Semiformula.subst_nil_eq_self] using h
  | n + 1, φ, u, W, hn, hu, hφ, hW4, hW, h => by
      have hn' : n ≤ 6 := by omega
      set χ := (shs n φ).subst (fvVec n).q
      have hAφ : (∀⁰ φ).val ≤ lvB (u + 2) := by
        have : (∀⁰ φ).val = ^∀ φ.val := by simp
        rw [this]
        exact pair_lvB hu (tag_le_lvB (by norm_num) hu) hφ
      have hcast : ((n + 1 : ℕ) : V) = (n : V) + 1 := by push_cast; rfl
      -- the formula after the step and its universal closure
      have hFv : χ.free.val ≤ lvB (sβ (u + n) + 1) := by
        rw [free_fvVec]
        refine lift_lvB (tsubst_le _ _ (shs_level φ hφ (n + 1)) (by norm_num) (fvVec_le hn)) ?_
        unfold sβ
        rw [hcast]
        exact le_of_add_eq (y := 11) (by ring)
      have hAv : (∀⁰ χ).val ≤ lvB (sβ (u + n)) := by
        have e : ∀⁰ χ = (shs n (∀⁰ φ)).subst (fvVec n) := by
          rw [shs_all, Bootstrapping.Semiformula.substs_all]
        rw [e]
        refine lift_lvB (tsubst_le _ _ (shs_level _ hAφ n) (by norm_num) (fvVec_le hn')) ?_
        unfold sβ
        exact le_of_eq (by ring)
      have hmW : sβ (u + n) + 1 + 1 ≤ W := by
        refine le_trans ?_ hW
        unfold sβ
        rw [hcast]
        exact le_of_add_eq (y := 20 * (n : V) + 29) (by ring)
      have d1 := all_step hW4 hAv hFv hmW (by rw [free_fvVec]; exact h)
      have e2 : ∀⁰ χ = (shs n (∀⁰ φ)).subst (fvVec n) := by
        rw [shs_all, Bootstrapping.Semiformula.substs_all]
      rw [e2] at d1
      have ih := strip n (∀⁰ φ) (u + 2) (W + 1 + 1) hn' (le_trans hu le_self_add) hAφ
        (le_trans hW4 (le_trans le_self_add le_self_add)) (by
          refine le_trans ?_ (le_trans hW (le_trans le_self_add le_self_add))
          unfold sβ
          rw [hcast]
          exact le_of_add_eq (y := 10) (by ring)) d1
      have e3 : W + 1 + 1 + 2 * (n : V) = W + 2 * ((n + 1 : ℕ) : V) := by rw [hcast]; ring
      rw [e3] at ih
      exact ih

/-! ## Complexity is at most the level -/

set_option maxHeartbeats 1000000 in
theorem complexity_le : ∀ u x : V, x ≤ lvB u → IsUFormula ℒₛₑₜ x → formulaComplexity ℒₛₑₜ x ≤ u := by
  intro u
  induction u using ISigma1.pi1_succ_induction
  · simp only [lvB]
    definability
  · intro x hx hxF
    exact absurd rfl (formula_level_pos hx hxF)
  · case succ u ih =>
    intro x hx hxF
    rcases hxF.case with ⟨k, R, v, hR, hv, rfl⟩ | ⟨k, R, v, hR, hv, rfl⟩ | rfl | rfl |
        ⟨p, q, hp, hq, rfl⟩ | ⟨p, q, hp, hq, rfl⟩ | ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
    · rw [formulaComplexity_rel hR hv]; exact Arithmetic.zero_le _
    · rw [formulaComplexity_nrel hR hv]; exact Arithmetic.zero_le _
    · simp
    · simp
    · rw [formulaComplexity_and hp hq]
      have hx' : ⟪(4 : V), ⟪p, q⟫⟫ + 1 ≤ lvB (u + 1) := hx
      have hY := (pair_children hx').2
      exact _root_.add_le_add (max_le (ih p (le_trans (le_pair_left _ _) hY) hp)
        (ih q (le_trans (le_pair_right _ _) hY) hq)) le_rfl
    · rw [formulaComplexity_or hp hq]
      have hx' : ⟪(5 : V), ⟪p, q⟫⟫ + 1 ≤ lvB (u + 1) := hx
      have hY := (pair_children hx').2
      exact _root_.add_le_add (max_le (ih p (le_trans (le_pair_left _ _) hY) hp)
        (ih q (le_trans (le_pair_right _ _) hY) hq)) le_rfl
    · rw [formulaComplexity_all hp]
      have hx' : ⟪(6 : V), p⟫ + 1 ≤ lvB (u + 1) := hx
      exact _root_.add_le_add (ih p (pair_children hx').2 hp) le_rfl
    · rw [formulaComplexity_ex hp]
      have hx' : ⟪(7 : V), p⟫ + 1 ≤ lvB (u + 1) := hx
      exact _root_.add_le_add (ih p (pair_children hx').2 hp) le_rfl

/-! ## Symmetry, bounded -/

local prefix:max "#'" => Bootstrapping.Semiterm.bvar (V := V) (L := ℒₛₑₜ)
local infix:46 " ≐ₛ " => SetCongruence.eqAtom

/-- `∀ x y, x = y → y = x`. -/
def symmSent : SetTheorySentence := ∀⁰ ∀⁰ (SetCongruence.sEq #1 #0 🡒 SetCongruence.sEq #0 #1)

theorem zf_symm : 𝗭𝗙 ⊢ symmSent := by
  refine SetTheory.provable_of_models.{0} 𝗭𝗙 _ ?_
  intro M _ _ _
  simp [symmSent, models_iff, SetCongruence.sEq]

def symmProof : 𝗭𝗙 ⊢! symmSent := zf_symm.get
def symmD : ℕ := ⌜symmProof⌝
def symmN : ℕ := ⌜symmSent⌝

def symmBody : Bootstrapping.Semiformula V ℒₛₑₜ 2 := ((#'1) ≐ₛ (#'0)) 🡒 ((#'0) ≐ₛ (#'1))

theorem symm_quote : (⌜symmSent⌝ : Bootstrapping.Formula V ℒₛₑₜ) = ∀⁰ ∀⁰ symmBody := by
  rw [Sentence.typed_quote_def]
  simp [symmSent, symmBody, SetCongruence.sEq, SetCongruence.eqAtom, Rew.q_emb, Rew.emb_bvar,
    SetCongruence.quote_vec2_eta]

theorem symm_dlv : DLv 𝗭𝗙 (insert (∀⁰ ∀⁰ symmBody : Bootstrapping.Formula V ℒₛₑₜ).val ∅)
    (symmD : V) := by
  have hp : Proof 𝗭𝗙 (⌜symmProof⌝ : V) ⌜symmSent⌝ := proof_of_quote_proof symmProof
  rw [Sentence.quote_eq, symm_quote] at hp
  rw [← singleton_eq_insert]
  unfold symmD
  rw [coe_quote_proof_eq]
  exact DLv.of_derivationOf hp

theorem symm_le : (∀⁰ ∀⁰ symmBody : Bootstrapping.Formula V ℒₛₑₜ).val ≤ lvB (symmN : V) := by
  rw [← symm_quote, ← Sentence.quote_eq, symmN, Sentence.coe_quote_eq_quote]
  exact le_lvB_self _

/-- The working level of a symmetry cut at variable level `c`. -/
def sW (c : V) : V := (symmD : V) + 10 * (10 * ((symmN : V) + 1) + c + 1) + 1

theorem sW_m (c : V) : 10 * (10 * ((symmN : V) + 1) + c + 1) + 1 ≤ sW c :=
  le_of_add_eq (y := (symmD : V)) (by unfold sW; ring)

theorem sW_D (c : V) : (symmD : V) ≤ sW c :=
  le_of_add_eq (y := 10 * (10 * ((symmN : V) + 1) + c + 1) + 1) (by unfold sW; ring)

theorem sW_four (c : V) : 4 ≤ sW c :=
  le_of_add_eq (y := (symmD : V) + 100 * symmN + 10 * c + 107) (by unfold sW; ring)

set_option maxHeartbeats 1000000 in
/-- **A symmetry cut**: the hypothesis `y ≠ x` can be dropped when `x ≠ y`
is present. -/
theorem symcut {x y Γ c W : V} (hx : IsSemiterm ℒₛₑₜ 0 x) (hy : IsSemiterm ℒₛₑₜ 0 y)
    (lx : x ≤ lvB c) (ly : y ≤ lvB c) (hc : 1 ≤ c) (hW : sW c ≤ W)
    (hΓ : SeqLe Γ (10 * (10 * ((symmN : V) + 1) + c + 1))) (hfs : IsFormulaSet ℒₛₑₜ Γ)
    (hxy : neR x y ∈ Γ) (h : DLv 𝗭𝗙 (insert (neR y x) Γ) W) :
    DLv 𝗭𝗙 Γ (W + 1 + 3 + 3 + 1 + 1) := by
  set tx := mkT x hx
  set ty := mkT y hy
  set m := 10 * ((symmN : V) + 1) + c with hm
  have hw : 10 * (m + 1) + 1 ≤ W := le_trans (sW_m c) hW
  have hw4 : 4 ≤ W := le_trans (sW_four c) hW
  have hm1 : m + 1 ≤ W := le_trans le_ten hw
  have hNm : (symmN : V) ≤ m := le_trans (le_trans le_self_add
    (le_mul_of_one_le_left (Arithmetic.zero_le _) (by norm_num))) le_self_add
  have hcm : c ≤ m := le_add_self
  -- the equality atoms
  have e_yx : (ty ≐ₛ tx).val = ^rel 2 (0 : V) (y ∷ x ∷ 0) := eqAtom_val ty tx
  have e_xy : (tx ≐ₛ ty).val = ^rel 2 (0 : V) (x ∷ y ∷ 0) := eqAtom_val tx ty
  have n_yx : (∼(ty ≐ₛ tx)).val = neR y x := by
    rw [Bootstrapping.Semiformula.val_neg, e_yx]; exact neg_eq_atom hy hx
  have n_xy : (∼(tx ≐ₛ ty)).val = neR x y := by
    rw [Bootstrapping.Semiformula.val_neg, e_xy]; exact neg_eq_atom hx hy
  have lEq : ∀ {a b : V}, a ≤ lvB c → b ≤ lvB c →
      ^rel 2 (0 : V) (a ∷ b ∷ 0) ≤ lvB (10 * (m + 1)) := fun ha hb =>
    lift_lvB (atom_le hc (by simp) (Or.inl rfl) ha hb)
      (le_of_add_eq (y := 100 * (symmN : V) + 9 * c + 99) (by rw [hm]; ring))
  have lNe : ∀ {a b : V}, a ≤ lvB c → b ≤ lvB c → neR a b ≤ lvB (10 * (m + 1)) := fun ha hb =>
    lift_lvB (atom_le hc le_rfl (Or.inl rfl) ha hb)
      (le_of_add_eq (y := 100 * (symmN : V) + 9 * c + 99) (by rw [hm]; ring))
  -- `Γ' := y = x, Γ`, and the instance `I := x = y → y = x` on it
  set Γ' := insert (^rel 2 (0 : V) (y ∷ x ∷ 0)) Γ with hΓ'
  have lΓ' : SeqLe Γ' (10 * (m + 1)) := hΓ.insert (lEq ly lx)
  have fΓ' : IsFormulaSet ℒₛₑₜ Γ' := by rw [hΓ', ← e_yx]; exact formulaSet_insert hfs
  set I : Bootstrapping.Formula V ℒₛₑₜ := (tx ≐ₛ ty) 🡒 (ty ≐ₛ tx) with hI
  have hX₀ : (∀⁰ ∀⁰ symmBody : Bootstrapping.Formula V ℒₛₑₜ).val ≤ lvB m := lift_lvB symm_le hNm
  have hY₁ : ((∀⁰ symmBody).subst ![tx]).val ≤ lvB m :=
    tsubst_le _ _ (body_le symm_le) hc (vec1_le lx)
  have hY₂ : (symmBody.subst ![ty, tx]).val ≤ lvB m :=
    tsubst_le _ _ (body_le (body_le symm_le)) hc (vec2_le ly lx)
  have d0 : DLv 𝗭𝗙 (insert (∀⁰ ∀⁰ symmBody : Bootstrapping.Formula V ℒₛₑₜ).val Γ') (W + 1) :=
    DLv.wk hw4 ((lΓ'.toLt hw).insert (lt_lvB_of hX₀ hm1)) (formulaSet_insert fΓ')
      (insert_subset_insert_of_subset _ (by intro z hz; simp at hz)) (symm_dlv.mono
        (le_trans (sW_D c) hW))
  have up : ∀ k : V, 10 * (m + 1) + 1 ≤ W + k := fun k => le_trans hw le_self_add
  have up4 : ∀ k : V, 4 ≤ W + k := fun k => le_trans hw4 le_self_add
  have d1 := spec_step (φ := ∀⁰ symmBody) (t := tx) rfl rfl hX₀ hY₁ (lift_lvB lx hcm) (up 1)
    (up4 1) ((lΓ'.toLt hw).mono le_self_add) fΓ' d0
  have d2 := spec_step (φ := symmBody.subst (Bootstrapping.SemitermVec.q ![tx])) (t := ty)
    (Bootstrapping.Semiformula.substs_all _ _).symm (subst_q_sing _ _ _) hY₁ hY₂
    (lift_lvB ly hcm) (by simpa [add_assoc] using up (1 + 3))
    (by simpa [add_assoc] using up4 (1 + 3))
    ((lΓ'.toLt hw).mono (by simpa [add_assoc] using (le_self_add : W ≤ W + (1 + 3)))) fΓ' d1
  have hIs : symmBody.subst ![ty, tx] = I := by simp [symmBody, hI, SetCongruence.eqAtom]
  rw [hIs] at d2 hY₂
  -- the negative side: `x = y ∧ y ≠ x`
  have hNI : (∼I).val = ^rel 2 (0 : V) (x ∷ y ∷ 0) ^⋏ neR y x := by
    have : ∼I = (tx ≐ₛ ty) ⋏ ∼(ty ≐ₛ tx) := by simp [hI, Bootstrapping.Semiformula.imp_def]
    rw [this, Bootstrapping.Semiformula.val_and, e_xy, n_yx]
  set S := insert (∼I).val Γ' with hS
  have lNI : (∼I).val ≤ lvB (10 * (m + 1)) := by
    rw [Bootstrapping.Semiformula.val_neg]; exact neg_level _ _ hY₂ I.isSemiformula.isUFormula
  have lS : SeqLe S (10 * (m + 1)) := lΓ'.insert lNI
  have fS : IsFormulaSet ℒₛₑₜ S := formulaSet_insert fΓ'
  have fNI := (∼I).isSemiformula
  rw [hNI] at fNI
  have dL : DLv 𝗭𝗙 (insert (^rel 2 (0 : V) (x ∷ y ∷ 0)) S) (W + 1) := by
    refine DLv.em hw4 ((lS.insert (lEq lx ly)).toLt hw) (IsFormulaSet.insert_iff.mpr ⟨(IsSemiformula.and.mp fNI).1, fS⟩)
      (^rel 2 (0 : V) (x ∷ y ∷ 0)) (by simp) ?_
    rw [neg_eq_atom hx hy]
    simp [hS, hΓ', hxy]
  have dR : DLv 𝗭𝗙 (insert (neR y x) S) (W + 1) := by
    refine DLv.em hw4 ((lS.insert (lNe ly lx)).toLt hw) (IsFormulaSet.insert_iff.mpr ⟨(IsSemiformula.and.mp fNI).2, fS⟩)
      (neR y x) (by simp) ?_
    have : neg ℒₛₑₜ (neR y x) = ^rel 2 (0 : V) (y ∷ x ∷ 0) := by
      unfold neR; exact neg_nrel (isRel_R (Or.inl rfl)) (by simp [hx.isUTerm, hy.isUTerm])
    rw [this]
    simp [hS, hΓ']
  have dN : DLv 𝗭𝗙 S (W + 1 + 1) :=
    DLv.and_m (up4 1) ((lS.toLt hw).mono le_self_add) (p := ^rel 2 (0 : V) (x ∷ y ∷ 0))
      (q := neR y x) (by rw [hS, hNI]; simp) dL dR
  -- cut on `I` gives `y = x, Γ`; cut on `y = x` gives `Γ`
  have hL13 : W + 1 + 1 ≤ W + 1 + 3 + 3 := le_of_add_eq (y := 5) (by ring)
  have dΓ' : DLv 𝗭𝗙 Γ' (W + 1 + 3 + 3 + 1) :=
    DLv.cut (by simpa [add_assoc] using up4 (1 + 3 + 3))
      ((lΓ'.toLt hw).mono (by simpa [add_assoc] using (le_self_add : W ≤ W + (1 + 3 + 3))))
      I.val (lt_lvB_of hY₂ (le_trans hm1 (by simpa [add_assoc] using
        (le_self_add : W ≤ W + (1 + 3 + 3))))) d2
      (by rw [← Bootstrapping.Semiformula.val_neg]; exact dN.mono hL13)
  refine DLv.cut (by simpa [add_assoc] using up4 (1 + 3 + 3 + 1))
    ((hΓ.toLt hw).mono (by simpa [add_assoc] using (le_self_add : W ≤ W + (1 + 3 + 3 + 1))))
    (^rel 2 (0 : V) (y ∷ x ∷ 0))
    (lt_lvB_of (lEq ly lx) (by simpa [add_assoc] using up (1 + 3 + 3 + 1))) dΓ' ?_
  rw [neg_eq_atom hy hx]
  exact h.mono (le_of_add_eq (y := 8) (by ring))

end LeanProofs.ZFCinPA.SizedPlaceholderCongruence
