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
open LeanProofs.BoundedPAConsistency.SizedDerivation LeanProofs.BoundedPAConsistency.SubstBound
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

theorem fvar_small : ∀ j : ℕ, j ≤ 6 → (^&(j : V) : V) ≤ lvB 3 := by
  intro j hj
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by omega
  rcases hj' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rw [lvB_three] <;> simp [qqFvar, pair] <;> norm_num

theorem fvVec_bound {n : ℕ} {c : V}
    (h : ∀ j : ℕ, j ≤ n → (^&(j : V) : V) ≤ lvB c) :
    ∀ i, ((fvVec (V := V) n) i).val ≤ lvB c := fun i => by
  simpa [fvVec] using h i (le_of_lt i.isLt)

theorem fvVec_le {n : ℕ} (hn : n ≤ 6) : ∀ j, ((fvVec (V := V) n) j).val ≤ lvB 3 :=
  fvVec_bound (fun j hj => fvar_small j (le_trans hj hn))

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
      have hχ : ∀⁰ χ = (shs n (∀⁰ φ)).subst (fvVec n) := by
        rw [shs_all, Bootstrapping.Semiformula.substs_all]
      have hAv : (∀⁰ χ).val ≤ lvB (sβ (u + n)) := by
        rw [hχ]
        refine lift_lvB (tsubst_le _ _ (shs_level _ hAφ n) (by norm_num) (fvVec_le hn')) ?_
        unfold sβ
        exact le_of_eq (by ring)
      have hmW : sβ (u + n) + 1 + 1 ≤ W := by
        refine le_trans ?_ hW
        unfold sβ
        rw [hcast]
        exact le_of_add_eq (y := 20 * (n : V) + 29) (by ring)
      have d1 := all_step hW4 hAv hFv hmW (by rw [free_fvVec]; exact h)
      rw [hχ] at d1
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
  have lAtom : ∀ {tag a b : V}, tag ≤ 1 → a ≤ lvB c → b ≤ lvB c →
      ⟪tag, 2, 0, a ∷ b ∷ 0⟫ + 1 ≤ lvB (10 * (m + 1)) := fun ht ha hb =>
    lift_lvB (atom_le hc ht (Or.inl rfl) ha hb)
      (le_of_add_eq (y := 100 * (symmN : V) + 9 * c + 99) (by rw [hm]; ring))
  have lEq : ∀ {a b : V}, a ≤ lvB c → b ≤ lvB c →
      ^rel 2 (0 : V) (a ∷ b ∷ 0) ≤ lvB (10 * (m + 1)) := lAtom (by simp)
  have lNe : ∀ {a b : V}, a ≤ lvB c → b ≤ lvB c → neR a b ≤ lvB (10 * (m + 1)) := lAtom le_rfl
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
  have d1 := spec_step_up (k := 1) (φ := ∀⁰ symmBody) (t := tx) rfl rfl hX₀ hY₁
    (lift_lvB lx hcm) hw hw4 (lΓ'.toLt hw) fΓ' d0
  have d2 := spec_step_up (k := 1 + 3) (φ := symmBody.subst (Bootstrapping.SemitermVec.q ![tx])) (t := ty)
    (Bootstrapping.Semiformula.substs_all _ _).symm (subst_q_sing _ _ _) hY₁ hY₂
    (lift_lvB ly hcm) hw hw4 (lΓ'.toLt hw) fΓ' (by simpa [add_assoc] using d1)
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
        (le_self_add : W ≤ W + (1 + 3 + 3))))) (by simpa [add_assoc] using d2)
      (by rw [← Bootstrapping.Semiformula.val_neg]; exact dN.mono hL13)
  refine DLv.cut (by simpa [add_assoc] using up4 (1 + 3 + 3 + 1))
    ((hΓ.toLt hw).mono (by simpa [add_assoc] using (le_self_add : W ≤ W + (1 + 3 + 3 + 1))))
    (^rel 2 (0 : V) (y ∷ x ∷ 0))
    (lt_lvB_of (lEq ly lx) (by simpa [add_assoc] using up (1 + 3 + 3 + 1))) dΓ' ?_
  rw [neg_eq_atom hy hx]
  exact h.mono (le_of_add_eq (y := 8) (by ring))

/-! ## Taking the context apart -/

/-- `S` with the negations `∼f j` adjoined. -/
def negsIns : {a : ℕ} → (Fin a → Bootstrapping.Formula V ℒₛₑₜ) → V → V
  | 0, _, S => S
  | _ + 1, f, S => insert (∼f 0).val (negsIns (Matrix.vecTail f) S)

theorem mem_negsIns : ∀ {a : ℕ} (f : Fin a → Bootstrapping.Formula V ℒₛₑₜ) (S y : V),
    y ∈ negsIns f S ↔ (∃ j, y = (∼f j).val) ∨ y ∈ S
  | 0, f, S, y => by simp [negsIns]
  | a + 1, f, S, y => by
      simp only [negsIns, mem_bitInsert_iff, mem_negsIns (Matrix.vecTail f)]
      constructor
      · rintro (rfl | ⟨j, rfl⟩ | h)
        · exact Or.inl ⟨0, rfl⟩
        · exact Or.inl ⟨j.succ, rfl⟩
        · exact Or.inr h
      · rintro (⟨j, rfl⟩ | h)
        · cases j using Fin.cases with
          | zero => exact Or.inl rfl
          | succ j => exact Or.inr (Or.inl ⟨j, rfl⟩)
        · exact Or.inr (Or.inr h)

theorem negsIns_le {a : ℕ} {f : Fin a → Bootstrapping.Formula V ℒₛₑₜ} {S m : V}
    (hf : ∀ j, (∼f j).val ≤ lvB m) (hS : SeqLe S m) : SeqLe (negsIns f S) m := by
  intro y hy
  rcases (mem_negsIns f S y).mp hy with ⟨j, rfl⟩ | h
  · exact hf j
  · exact hS y h

theorem negsIns_formulaSet {a : ℕ} {f : Fin a → Bootstrapping.Formula V ℒₛₑₜ} {S : V}
    (hS : IsFormulaSet ℒₛₑₜ S) : IsFormulaSet ℒₛₑₜ (negsIns f S) := by
  intro y hy
  rcases (mem_negsIns f S y).mp hy with ⟨j, rfl⟩ | h
  · exact (∼f j).isSemiformula
  · exact hS y h

theorem conj_succ {n a : ℕ} (f : Fin (a + 1) → Bootstrapping.Semiformula V ℒₛₑₜ n) :
    Matrix.conj f = f 0 ⋏ Matrix.conj (Matrix.vecTail f) := rfl

/-- **Unpacking a negated conjunction.** -/
theorem unpack : ∀ {a : ℕ} (f : Fin a → Bootstrapping.Formula V ℒₛₑₜ) (S W m : V), 4 ≤ W →
    m + 1 ≤ W → (∼Matrix.conj f).val ∈ S → (∼Matrix.conj f).val ≤ lvB m →
    (∀ j, (∼f j).val ≤ lvB m) → SeqLe S m → IsFormulaSet ℒₛₑₜ S →
    DLv 𝗭𝗙 (negsIns f S) W → DLv 𝗭𝗙 S (W + 2 * a)
  | 0, f, S, W, m, _, _, _, _, _, _, _, h => by simpa [negsIns] using h
  | a + 1, f, S, W, m, hW4, hmW, hmem, hl, hf, hS, hfs, h => by
      have ev : (∼Matrix.conj f).val = (∼f 0).val ^⋎ (∼Matrix.conj (Matrix.vecTail f)).val := by
        rw [conj_succ]; simp
      set S' := insert (∼f 0).val (insert (∼Matrix.conj (Matrix.vecTail f)).val S) with hS'
      have l1 : (∼Matrix.conj (Matrix.vecTail f)).val ≤ lvB m :=
        le_trans (le_of_lt (lt_or_right _ _)) (ev ▸ hl)
      have lS' : SeqLe S' m := (hS.insert l1).insert (hf 0)
      have fS' : IsFormulaSet ℒₛₑₜ S' := formulaSet_insert (formulaSet_insert hfs)
      have hft : ∀ j, (∼(Matrix.vecTail f) j).val ≤ lvB m := fun j => hf j.succ
      have h' : DLv 𝗭𝗙 (negsIns (Matrix.vecTail f) S') (W + 1) := by
        refine DLv.wk hW4 ((negsIns_le hft lS').toLt hmW) (negsIns_formulaSet fS') ?_ h
        intro y hy
        simp only [negsIns, mem_bitInsert_iff] at hy
        rw [mem_negsIns]
        rcases hy with rfl | hy
        · exact Or.inr (by simp [hS'])
        · rcases (mem_negsIns _ S y).mp hy with ⟨j, rfl⟩ | hy
          · exact Or.inl ⟨j, rfl⟩
          · exact Or.inr (by simp [hS', hy])
      have ih := unpack (Matrix.vecTail f) S' (W + 1) m (le_trans hW4 le_self_add)
        (le_trans hmW le_self_add) (by simp [hS']) l1 hft lS' fS' h'
      have hWa : W ≤ W + 1 + 2 * (a : V) := le_trans le_self_add le_self_add
      have d := DLv.or_m (le_trans hW4 hWa) (hS.toLt (le_trans hmW hWa))
        (p := (∼f 0).val) (q := (∼Matrix.conj (Matrix.vecTail f)).val) (ev ▸ hmem) ih
      have e : W + 1 + 2 * (a : V) + 1 = W + 2 * ((a + 1 : ℕ) : V) := by push_cast; ring
      rw [← e]
      exact d

/-! ## The shape of the stripped body -/

theorem shs_imp {n : ℕ} (φ ψ : Bootstrapping.Semiformula V ℒₛₑₜ n) :
    ∀ k : ℕ, shs k (φ 🡒 ψ) = shs k φ 🡒 shs k ψ
  | 0 => rfl
  | k + 1 => by rw [shs_succ, shs_succ, shs_succ, shs_imp φ ψ k, Bootstrapping.Semiformula.shift_imp]

theorem shs_and {n : ℕ} (φ ψ : Bootstrapping.Semiformula V ℒₛₑₜ n) :
    ∀ k : ℕ, shs k (φ ⋏ ψ) = shs k φ ⋏ shs k ψ
  | 0 => rfl
  | k + 1 => by rw [shs_succ, shs_succ, shs_succ, shs_and φ ψ k, Bootstrapping.Semiformula.shift_and]

theorem shs_verum {n : ℕ} : ∀ k : ℕ, shs k (⊤ : Bootstrapping.Semiformula V ℒₛₑₜ n) = ⊤
  | 0 => rfl
  | k + 1 => by rw [shs_succ, shs_verum k, Bootstrapping.Semiformula.shift_verum]

theorem shs_eqAtom {n : ℕ} (t u : Bootstrapping.Semiterm V ℒₛₑₜ n) :
    ∀ k : ℕ, shs k (t ≐ₛ u) =
      ((Bootstrapping.Semiterm.shift)^[k] t ≐ₛ (Bootstrapping.Semiterm.shift)^[k] u)
  | 0 => rfl
  | k + 1 => by
      rw [shs_succ, shs_eqAtom t u k, SetCongruence.eqAtom_shift, Function.iterate_succ_apply',
        Function.iterate_succ_apply']

theorem shs_conj {n : ℕ} : ∀ {a : ℕ} (f : Fin a → Bootstrapping.Semiformula V ℒₛₑₜ n) (k : ℕ),
    shs k (Matrix.conj f) = Matrix.conj (fun j => shs k (f j))
  | 0, _, k => shs_verum k
  | a + 1, f, k => by
      rw [conj_succ, shs_and, shs_conj (Matrix.vecTail f) k, conj_succ]
      rfl

theorem subst_conj {n m : ℕ} (w : Bootstrapping.SemitermVec V ℒₛₑₜ n m) :
    ∀ {a : ℕ} (f : Fin a → Bootstrapping.Semiformula V ℒₛₑₜ n),
      (Matrix.conj f).subst w = Matrix.conj (fun j => (f j).subst w)
  | 0, _ => by simp [Matrix.conj]
  | a + 1, f => by
      rw [conj_succ, Bootstrapping.Semiformula.substs_and, subst_conj w (Matrix.vecTail f), conj_succ]
      rfl

theorem shs_subst {a m : ℕ} (K : Bootstrapping.Semiformula V ℒₛₑₜ a)
    (w : Bootstrapping.SemitermVec V ℒₛₑₜ a m) :
    ∀ k : ℕ, shs k (K.subst w) = (shs k K).subst (fun j => (Bootstrapping.Semiterm.shift)^[k] (w j))
  | 0 => rfl
  | k + 1 => by
      rw [shs_succ, shs_subst K w k, Bootstrapping.Semiformula.shift_substs, shs_succ]
      congr 1
      funext j
      simp [Function.iterate_succ_apply']

theorem shift_iter_bvar {n : ℕ} (i : Fin n) :
    ∀ k : ℕ, (Bootstrapping.Semiterm.shift)^[k] (Bootstrapping.Semiterm.bvar i : Bootstrapping.Semiterm V ℒₛₑₜ n) =
      Bootstrapping.Semiterm.bvar i
  | 0 => rfl
  | k + 1 => by rw [Function.iterate_succ_apply', shift_iter_bvar i k]; simp

/-- The left and right variables after stripping: `&j` and `&(j + a)`. -/
def xVec (a : ℕ) : Bootstrapping.SemitermVec V ℒₛₑₜ a 0 :=
  fun j => Bootstrapping.Semiterm.fvar ((j : ℕ) : V)

def yVec (a : ℕ) : Bootstrapping.SemitermVec V ℒₛₑₜ a 0 :=
  fun j => Bootstrapping.Semiterm.fvar (((j : ℕ) + a : ℕ) : V)

theorem body_shape (a : ℕ) (K : Bootstrapping.Semiformula V ℒₛₑₜ a) :
    (shs (a + a) (SetCongruence.congruenceContext a 🡒 K.subst (SetCongruence.leftTuple a) 🡒
        K.subst (SetCongruence.rightTuple a))).subst (fvVec (a + a)) =
      Matrix.conj (fun j : Fin a => xVec a j ≐ₛ yVec a j) 🡒
        (shs (a + a) K).subst (xVec a) 🡒 (shs (a + a) K).subst (yVec a) := by
  rw [shs_imp, shs_imp, Bootstrapping.Semiformula.substs_imp, Bootstrapping.Semiformula.substs_imp]
  congr 1
  · unfold SetCongruence.congruenceContext
    rw [shs_conj, subst_conj]
    congr 1
    funext j
    rw [shs_eqAtom, SetCongruence.eqAtom_subst]
    simp [SetCongruence.leftTuple, SetCongruence.rightTuple, shift_iter_bvar, fvVec, xVec, yVec]
  · congr 1
    · rw [shs_subst, Bootstrapping.Semiformula.substs_substs]
      congr 1
      funext j
      simp [SetCongruence.leftTuple, shift_iter_bvar, fvVec, xVec]
    · rw [shs_subst, Bootstrapping.Semiformula.substs_substs]
      congr 1
      funext j
      simp [SetCongruence.rightTuple, shift_iter_bvar, fvVec, yVec]

/-! ## Dropping all reversed hypotheses -/

theorem symcuts : ∀ {a : ℕ} (f g : Fin a → Bootstrapping.Formula V ℒₛₑₜ) (T W c : V), 1 ≤ c →
    sW c ≤ W →
    (∀ j, ∃ x y, IsSemiterm ℒₛₑₜ 0 x ∧ IsSemiterm ℒₛₑₜ 0 y ∧ x ≤ lvB c ∧ y ≤ lvB c ∧
      (∼f j).val = neR x y ∧ (∼g j).val = neR y x) →
    (∀ j, (∼f j).val ∈ T) → SeqLe T (10 * (10 * ((symmN : V) + 1) + c + 1)) →
    IsFormulaSet ℒₛₑₜ T → (∀ j, (∼g j).val ≤ lvB (10 * (10 * ((symmN : V) + 1) + c + 1))) →
    DLv 𝗭𝗙 (negsIns g T) W → DLv 𝗭𝗙 T (W + 9 * a)
  | 0, _, _, T, W, _, _, _, _, _, _, _, _, h => by simpa [negsIns] using h
  | a + 1, f, g, T, W, c, hc, hW, hfg, hfT, hT, hfs, hgb, h => by
      obtain ⟨x, y, hx, hy, lx, ly, ef, eg⟩ := hfg 0
      have hgb' : ∀ j, (∼(Matrix.vecTail g) j).val ≤ lvB (10 * (10 * ((symmN : V) + 1) + c + 1)) :=
        fun j => hgb j.succ
      have hxy : neR x y ∈ negsIns (Matrix.vecTail g) T :=
        (mem_negsIns _ T _).mpr (Or.inr (ef ▸ hfT 0))
      have h' : DLv 𝗭𝗙 (insert (neR y x) (negsIns (Matrix.vecTail g) T)) W := by
        rw [← eg]; exact h
      have d1 := symcut hx hy lx ly hc hW (negsIns_le hgb' hT) (negsIns_formulaSet hfs) hxy h'
      have ih := symcuts (Matrix.vecTail f) (Matrix.vecTail g) T (W + 1 + 3 + 3 + 1 + 1) c hc
        (le_trans hW (le_trans le_self_add (le_trans le_self_add (le_trans le_self_add
          (le_trans le_self_add le_self_add)))))
        (fun j => hfg j.succ) (fun j => hfT j.succ) hT hfs hgb' d1
      have e : W + 1 + 3 + 3 + 1 + 1 + 9 * (a : V) = W + 9 * ((a + 1 : ℕ) : V) := by
        push_cast; ring
      rw [e] at ih
      exact ih

/-! ## Level bounds for the pieces -/

theorem conn_le {tag p q m : V} (hm : 2 ≤ m) (ht : tag ≤ 16) (hp : p ≤ lvB m) (hq : q ≤ lvB m) :
    ⟪tag, ⟪p, q⟫⟫ + 1 ≤ lvB (m + 4) :=
  pair_lvB_le (le_trans hm le_self_add) (le_of_eq (by ring)) (tag_le_lvB ht (le_trans hm le_self_add))
    (pair_lvB' hm hp hq)

theorem verum_le {m : V} (hm : 2 ≤ m) : (^⊤ : V) ≤ lvB m :=
  le_trans (show (^⊤ : V) ≤ 16 by simp [qqVerum, pair]; norm_num) (le_trans (le_of_eq lvB_two.symm)
    (lvB_mono hm))

theorem conj_le {n : ℕ} : ∀ {a : ℕ} (f : Fin a → Bootstrapping.Semiformula V ℒₛₑₜ n) {m : V},
    2 ≤ m → (∀ j, (f j).val ≤ lvB m) → (Matrix.conj f).val ≤ lvB (m + 4 * a)
  | 0, _, m, hm, _ => by simpa [Matrix.conj] using verum_le hm
  | a + 1, f, m, hm, hf => by
      rw [conj_succ, Bootstrapping.Semiformula.val_and]
      have ih := conj_le (Matrix.vecTail f) hm (fun j => hf j.succ)
      have h2 : 2 ≤ m + 4 * (a : V) := le_trans hm le_self_add
      have := conn_le (tag := 4) h2 (by norm_num) (lift_lvB (hf 0) le_self_add) ih
      refine le_trans this (le_of_eq ?_)
      congr 1
      push_cast
      ring

theorem bvar_small : ∀ j : ℕ, j ≤ 6 → (^#(j : V) : V) ≤ lvB 3 := by
  intro j hj
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by omega
  rcases hj' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rw [lvB_three] <;> simp [qqBvar, pair] <;> norm_num

/-- Substitution of variable terms, for typed vectors with bound variables. -/
theorem tsubst_le_var {k m : ℕ} (ψ : Bootstrapping.Semiformula V ℒₛₑₜ k)
    (v : Bootstrapping.SemitermVec V ℒₛₑₜ k m) {u c : V} (hψ : ψ.val ≤ lvB u) (hc : 1 ≤ c)
    (hv : ∀ i, (v i).val ≤ lvB c) (hvar : ∀ i, IsVarTerm (v i).val) :
    (ψ.subst v).val ≤ lvB (10 * (u + 1) + c) := by
  rw [Bootstrapping.Semiformula.val_substs]
  refine subst_level u ψ.val hψ ψ.isSemiformula.isUFormula c k m v.val hc
    (by simpa using v.isSemitermVec) ?_ ?_
  · intro i hi
    obtain ⟨j, rfl⟩ := eq_fin_of_lt_nat hi
    rw [Bootstrapping.SemitermVec.val_nth_eq]; exact hv j
  · intro i hi
    obtain ⟨j, rfl⟩ := eq_fin_of_lt_nat hi
    rw [Bootstrapping.SemitermVec.val_nth_eq]; exact hvar j

/-! ## The placeholder congruence leaf -/

/-- The member level of the leaf. -/
def mBig (u : V) : V := 100 * u + 748

/-- The level of the replacement core. -/
def coreL (u : V) : V := cW congA (u + 6) (u + 6) 14

/-- The level after the symmetry cuts start. -/
def lW₁ (u : V) : V := coreL u + 1 + sW (mBig u)

/-- **The level of the placeholder congruence leaf**, linear in `u`. -/
def congL (u : V) : V := lW₁ u + 47

theorem atom14 {tag R x y : V} (ht : tag ≤ 1) (hR : R = 0 ∨ R = 1) (hx : x ≤ lvB 3)
    (hy : y ≤ lvB 3) : ⟪tag, 2, R, x ∷ y ∷ 0⟫ + 1 ≤ lvB 14 := by
  have := atom_le (c := 3) (by norm_num) ht hR hx hy
  rwa [show (3 : V) + 1 + 10 = 14 by norm_num] at this

theorem four_a_le {a : ℕ} (ha : a ≤ 3) : 4 * (a : V) ≤ 12 := by
  have haV : (a : V) ≤ 3 := by exact_mod_cast ha
  have := mul_le_mul_of_nonneg_left haV (show (0 : V) ≤ 4 by norm_num)
  simpa using this.trans (le_of_eq (by norm_num))

theorem conj_atoms_le {n a : ℕ} (ha : a ≤ 3) (f : Fin a → Bootstrapping.Semiformula V ℒₛₑₜ n)
    (hf : ∀ j, (f j).val ≤ lvB 14) : (∼Matrix.conj f).val ≤ lvB 270 := by
  have h := lift_lvB (conj_le f (by norm_num) hf) (_root_.add_le_add le_rfl (four_a_le ha))
  rw [Bootstrapping.Semiformula.val_neg]
  have := neg_level _ _ h (Matrix.conj f).isSemiformula.isUFormula
  rwa [show 10 * ((14 : V) + 12 + 1) = 270 by norm_num] at this

set_option maxHeartbeats 4000000 in
/-- **The placeholder congruence leaf, bounded.** For every internal `K` of
arity `a ≤ 3` at level `u ≥ 2`, the congruence law `congruenceFormula a K`
has a `𝗭𝗙`-derivation with code at most `2^(lvB (congL u))`, and `congL u`
is linear in `u` with standard coefficients. -/
theorem cong_leaf (a : ℕ) (ha : a ≤ 3) (K : Bootstrapping.Semiformula V ℒₛₑₜ a) {u : V}
    (hu : 2 ≤ u) (hK : K.val ≤ lvB u) :
    DLv 𝗭𝗙 (insert (SetCongruence.congruenceFormula a K).val ∅) (congL u) := by
  have hn6 : a + a ≤ 6 := by omega
  have hnV : ((a + a : ℕ) : V) ≤ 6 := by exact_mod_cast hn6
  have haV : (a : V) ≤ 3 := by exact_mod_cast ha
  set K' := shs (a + a) K with hK'def
  have hK' : K'.val ≤ lvB (u + 6) := lift_lvB (shs_level K hK (a + a)) (_root_.add_le_add le_rfl hnV)
  set xv := xVec (V := V) a with hxvd
  set yv := yVec (V := V) a with hyvd
  have hxv : ∀ j, (xv j).val ≤ lvB 3 := fun j => by
    simpa [hxvd, xVec] using fvar_small j (by omega)
  have hyv : ∀ j, (yv j).val ≤ lvB 3 := fun j => by
    simpa [hyvd, yVec] using fvar_small (j + a) (by omega)
  have cx : ∀ j, IsSemiterm ℒₛₑₜ 0 (xv j).val := fun j => by simpa using (xv j).isSemiterm
  have cy : ∀ j, IsSemiterm ℒₛₑₜ 0 (yv j).val := fun j => by simpa using (yv j).isSemiterm
  set f : Fin a → Bootstrapping.Formula V ℒₛₑₜ := fun j => xv j ≐ₛ yv j with hf
  set g : Fin a → Bootstrapping.Formula V ℒₛₑₜ := fun j => yv j ≐ₛ xv j with hg
  have nf : ∀ j, (∼f j).val = neR (xv j).val (yv j).val := fun j => by
    rw [Bootstrapping.Semiformula.val_neg, hf, eqAtom_val]; exact neg_eq_atom (cx j) (cy j)
  have ng : ∀ j, (∼g j).val = neR (yv j).val (xv j).val := fun j => by
    rw [Bootstrapping.Semiformula.val_neg, hg, eqAtom_val]; exact neg_eq_atom (cy j) (cx j)
  have lf : ∀ j, (f j).val ≤ lvB 14 := fun j => by
    rw [hf, eqAtom_val]; exact atom14 (by simp) (Or.inl rfl) (hxv j) (hyv j)
  have lnf : ∀ j, (∼f j).val ≤ lvB 14 := fun j => by
    rw [nf]; exact atom14 le_rfl (Or.inl rfl) (hxv j) (hyv j)
  have lng : ∀ j, (∼g j).val ≤ lvB 14 := fun j => by
    rw [ng]; exact atom14 le_rfl (Or.inl rfl) (hyv j) (hxv j)
  -- the replacement core
  set E₀ := negsIns f (negsIns g (∅ : V)) with hE₀
  have hE₀l : SeqLe E₀ 14 :=
    negsIns_le lnf (negsIns_le lng (fun y hy => by simp at hy))
  have hE₀f : IsFormulaSet ℒₛₑₜ E₀ :=
    negsIns_formulaSet (negsIns_formulaSet (fun y hy => by simp at hy))
  have l314 : (3 : V) ≤ 14 := by norm_num
  have inp : Inp (a : V) xv.val yv.val E₀ 14 := by
    refine ⟨by simpa using xv.isSemitermVec, by simpa using yv.isSemitermVec, by norm_num,
      (tvec_entries xv (fun j => lift_lvB (hxv j) l314)).1,
      (tvec_entries yv (fun j => lift_lvB (hyv j) l314)).1, hE₀f, hE₀l, ?_⟩
    intro i hi
    obtain ⟨j, rfl⟩ := eq_fin_of_lt_nat hi
    rw [Bootstrapping.SemitermVec.val_nth_eq, Bootstrapping.SemitermVec.val_nth_eq]
    right
    constructor
    · rw [← nf]; exact (mem_negsIns _ _ _).mpr (Or.inl ⟨j, rfl⟩)
    · rw [← ng]; exact (mem_negsIns _ _ _).mpr (Or.inr ((mem_negsIns _ _ _).mpr (Or.inl ⟨j, rfl⟩)))
  have D0 := replace_le (u + 6) (u + 6) K'.val (a : V) xv.val yv.val E₀ 14
    (complexity_le _ _ hK' K'.isSemiformula.isUFormula) (by simpa using K'.isSemiformula) hK' inp
  -- the pieces of the stripped body
  set Kx := K'.subst xv with hKx
  set Ky := K'.subst yv with hKy
  have eKx : neg ℒₛₑₜ (subst ℒₛₑₜ xv.val K'.val) = (∼Kx).val := by
    rw [Bootstrapping.Semiformula.val_neg, Bootstrapping.Semiformula.val_substs]
  have eKy : subst ℒₛₑₜ yv.val K'.val = Ky.val := (Bootstrapping.Semiformula.val_substs _ _).symm
  set Lk := 10 * (10 * (u + 6 + 1) + 3 + 1) with hLk
  have lKx : Kx.val ≤ lvB (10 * (u + 6 + 1) + 3) := tsubst_le K' xv hK' (by norm_num) hxv
  have lKy : Ky.val ≤ lvB (10 * (u + 6 + 1) + 3) := tsubst_le K' yv hK' (by norm_num) hyv
  have lnKx : (∼Kx).val ≤ lvB Lk := by
    rw [Bootstrapping.Semiformula.val_neg]; exact neg_level _ _ lKx Kx.isSemiformula.isUFormula
  have hKyLk : 10 * (u + 6 + 1) + 3 ≤ Lk :=
    le_trans le_self_add (le_mul_of_one_le_left (Arithmetic.zero_le _) (by norm_num))
  have hLk2 : (2 : V) ≤ Lk := le_of_add_eq (y := 100 * u + 738) (by rw [hLk]; ring)
  set ctx := Matrix.conj f with hctx
  set R := Kx 🡒 Ky with hR
  set B' := ctx 🡒 R with hB'
  have eR : R.val = (∼Kx).val ^⋎ Ky.val := by
    rw [hR, Bootstrapping.Semiformula.imp_def, Bootstrapping.Semiformula.val_or]
  have eB : B'.val = (∼ctx).val ^⋎ R.val := by
    rw [hB', Bootstrapping.Semiformula.imp_def, Bootstrapping.Semiformula.val_or]
  have lR : R.val ≤ lvB (Lk + 4) := by
    rw [eR]; exact conn_le (tag := 5) hLk2 (by norm_num) lnKx (lift_lvB lKy hKyLk)
  have lnctx : (∼ctx).val ≤ lvB (Lk + 4) :=
    lift_lvB (conj_atoms_le ha f lf) (le_of_add_eq (y := 100 * u + 474) (by rw [hLk]; ring))
  have lB : B'.val ≤ lvB (mBig u) := by
    rw [eB]
    refine lift_lvB (conn_le (tag := 5) (le_trans hLk2 le_self_add) (by norm_num) lnctx lR) ?_
    exact le_of_eq (by rw [hLk]; unfold mBig; ring)
  have hLkM : Lk + 4 ≤ mBig u := le_of_add_eq (y := 4) (by rw [hLk]; unfold mBig; ring)
  have fctx := (∼ctx).isSemiformula
  have fR := R.isSemiformula
  have fB := B'.isSemiformula
  have fnKx := (∼Kx).isSemiformula
  have fKy := Ky.isSemiformula
  -- the sequents
  set S₂ := insert (∼ctx).val (insert R.val (insert B'.val (∅ : V))) with hS₂
  set S₁ := insert (∼Kx).val (insert Ky.val S₂) with hS₁
  set T₀ := negsIns f S₁ with hT₀
  set T₁ := negsIns g T₀ with hT₁
  have lS₂ : SeqLe S₂ (mBig u) :=
    ((SeqLe.insert lB (fun y hy => by simp at hy)).insert (lift_lvB lR hLkM)).insert
      (lift_lvB lnctx hLkM)
  have lS₁ : SeqLe S₁ (mBig u) :=
    (lS₂.insert (lift_lvB lKy (le_trans hKyLk (le_trans le_self_add hLkM)))).insert
      (lift_lvB lnKx (le_trans le_self_add hLkM))
  have h14 : (14 : V) ≤ mBig u := le_of_add_eq (y := 100 * u + 734) (by unfold mBig; ring)
  have lT₀ : SeqLe T₀ (mBig u) := negsIns_le (fun j => lift_lvB (lnf j) h14) lS₁
  have lT₁ : SeqLe T₁ (mBig u) := negsIns_le (fun j => lift_lvB (lng j) h14) lT₀
  have fS₂ : IsFormulaSet ℒₛₑₜ S₂ := by simp [hS₂, fctx, fR, fB]
  have fS₁ : IsFormulaSet ℒₛₑₜ S₁ := by simp [hS₁, fnKx, fKy, fS₂]
  have fT₀ : IsFormulaSet ℒₛₑₜ T₀ := negsIns_formulaSet fS₁
  have fT₁ : IsFormulaSet ℒₛₑₜ T₁ := negsIns_formulaSet fT₀
  -- D1: weaken the core into `T₁`
  have hcore4 : 4 ≤ coreL u := cW_four _ _ _ _
  have hcoreM : mBig u + 1 ≤ coreL u :=
    le_of_add_eq (y := 30 * u + 371 + congA) (by unfold mBig coreL cW; ring)
  have D1 : DLv 𝗭𝗙 T₁ (coreL u + 1) := by
    refine DLv.wk hcore4 (lT₁.toLt hcoreM) fT₁ ?_ D0
    intro z hz
    unfold Cseq at hz
    rw [eKx, eKy] at hz
    have hS₁T₁ : ∀ {y : V}, y ∈ S₁ → y ∈ T₁ := fun hy =>
      (mem_negsIns _ _ _).mpr (Or.inr ((mem_negsIns _ _ _).mpr (Or.inr hy)))
    rcases mem_bitInsert_iff.mp hz with rfl | hz
    · exact hS₁T₁ (by simp [hS₁])
    rcases mem_bitInsert_iff.mp hz with rfl | hz
    · exact hS₁T₁ (by simp [hS₁])
    rcases (mem_negsIns _ _ _).mp hz with ⟨j, rfl⟩ | hz
    · exact (mem_negsIns _ _ _).mpr (Or.inr ((mem_negsIns _ _ _).mpr (Or.inl ⟨j, rfl⟩)))
    rcases (mem_negsIns _ _ _).mp hz with ⟨j, rfl⟩ | hz
    · exact (mem_negsIns _ _ _).mpr (Or.inl ⟨j, rfl⟩)
    · simp at hz
  -- D2: the symmetry cuts
  have hM1 : (1 : V) ≤ mBig u := le_trans (by norm_num) h14
  have hMs : mBig u ≤ 10 * (10 * ((symmN : V) + 1) + mBig u + 1) :=
    le_trans (le_trans le_add_self le_self_add)
      (le_mul_of_one_le_left (Arithmetic.zero_le _) (by norm_num))
  have hsW : sW (mBig u) ≤ lW₁ u := le_add_self
  have D2 := symcuts f g T₀ (lW₁ u) (mBig u) hM1 hsW
    (fun j => ⟨(xv j).val, (yv j).val, cx j, cy j, lift_lvB (hxv j) (le_trans l314 h14),
      lift_lvB (hyv j) (le_trans l314 h14), nf j, ng j⟩)
    (fun j => (mem_negsIns _ _ _).mpr (Or.inl ⟨j, rfl⟩)) (lT₀.mono hMs) fT₀
    (fun j => lift_lvB (lng j) (le_trans h14 hMs))
    (D1.mono le_self_add)
  -- D3: unpack the context
  have hW₁M : mBig u + 1 ≤ lW₁ u :=
    le_trans (le_of_add_eq (y := (symmD : V) + 100 * symmN + 9 * mBig u + 110) (by unfold sW; ring)) hsW
  have hW₁4 : 4 ≤ lW₁ u := le_trans (le_trans (by norm_num : (4 : V) ≤ 14) (le_trans h14 le_self_add)) hW₁M
  have D3 := unpack f S₁ (lW₁ u + 9 * (a : V)) (mBig u) (le_trans hW₁4 le_self_add)
    (le_trans hW₁M le_self_add) (by simp [hS₁, hS₂, hctx]) (lift_lvB lnctx hLkM)
    (fun j => lift_lvB (lnf j) h14) lS₁ fS₁ D2
  -- D4, D5: the two disjunctions
  set W₂ := lW₁ u + 9 * (a : V) + 2 * (a : V) with hW₂
  have hW₂1 : lW₁ u ≤ W₂ := le_trans le_self_add le_self_add
  have D4 : DLv 𝗭𝗙 S₂ (W₂ + 1) :=
    DLv.or_m (le_trans hW₁4 hW₂1) (lS₂.toLt (le_trans hW₁M hW₂1)) (p := (∼Kx).val) (q := Ky.val)
      (by rw [← eR]; simp [hS₂]) D3
  have D5 : DLv 𝗭𝗙 (insert B'.val ∅) (W₂ + 1 + 1) :=
    DLv.or_m (le_trans hW₁4 (le_trans hW₂1 le_self_add))
      (((SeqLe.insert lB (fun y hy => by simp at hy))).toLt (le_trans hW₁M (le_trans hW₂1 le_self_add)))
      (p := (∼ctx).val) (q := R.val) (by rw [← eB]; simp) D4
  -- D6: restore the binders
  set body := SetCongruence.congruenceContext a 🡒 K.subst (SetCongruence.leftTuple a) 🡒
    K.subst (SetCongruence.rightTuple a) with hbody
  have hshape : (shs (a + a) body).subst (fvVec (a + a)) = B' := by
    rw [hbody]; exact body_shape a K
  have lbody : body.val ≤ lvB (100 * u + 300) := by
    have lt : ∀ j, ((SetCongruence.leftTuple (V := V) a) j).val ≤ lvB 3 ∧
        IsVarTerm ((SetCongruence.leftTuple (V := V) a) j).val := fun j => by
      refine ⟨by simpa [SetCongruence.leftTuple] using bvar_small j (by omega), ?_⟩
      simpa [SetCongruence.leftTuple] using isVarTerm_bvar ((j : ℕ) : V)
    have rt : ∀ j, ((SetCongruence.rightTuple (V := V) a) j).val ≤ lvB 3 ∧
        IsVarTerm ((SetCongruence.rightTuple (V := V) a) j).val := fun j => by
      refine ⟨by simpa [SetCongruence.rightTuple] using bvar_small (j + a) (by omega), ?_⟩
      simpa [SetCongruence.rightTuple] using isVarTerm_bvar (((j : ℕ) + a : ℕ) : V)
    have lKl := tsubst_le_var K (SetCongruence.leftTuple a) hK (by norm_num) (fun j => (lt j).1)
      (fun j => (lt j).2)
    have lKr := tsubst_le_var K (SetCongruence.rightTuple a) hK (by norm_num) (fun j => (rt j).1)
      (fun j => (rt j).2)
    have lnKl : (∼(K.subst (SetCongruence.leftTuple a))).val ≤ lvB (10 * (10 * (u + 1) + 3 + 1)) := by
      rw [Bootstrapping.Semiformula.val_neg]
      exact neg_level _ _ lKl (K.subst _).isSemiformula.isUFormula
    set m₁ := 10 * (10 * (u + 1) + 3 + 1) with hm₁
    have hm₁2 : (2 : V) ≤ m₁ := le_of_add_eq (y := 100 * u + 138) (by rw [hm₁]; ring)
    have lin : (K.subst (SetCongruence.leftTuple a) 🡒 K.subst (SetCongruence.rightTuple a)).val ≤
        lvB (m₁ + 4) := by
      rw [Bootstrapping.Semiformula.imp_def, Bootstrapping.Semiformula.val_or]
      exact conn_le (tag := 5) hm₁2 (by norm_num) lnKl (lift_lvB lKr
        (le_trans le_self_add (le_mul_of_one_le_left (Arithmetic.zero_le _) (by norm_num))))
    have latoms : ∀ j, (SetCongruence.leftTuple (V := V) a j ≐ₛ SetCongruence.rightTuple a j).val ≤ lvB 14 :=
      fun j => by
        rw [SetCongruence.val_eqAtom, SetCongruence.coe_setEqIndex_eq]
        exact atom14 (by simp) (Or.inl rfl) (lt j).1 (rt j).1
    have lnc : (∼SetCongruence.congruenceContext (V := V) a).val ≤ lvB (m₁ + 4) :=
      lift_lvB (conj_atoms_le ha _ latoms) (by
        calc (270 : V) ≤ 100 * 2 + 144 := by norm_num
          _ ≤ 100 * u + 144 := _root_.add_le_add (mul_le_mul_of_nonneg_left hu (by norm_num)) le_rfl
          _ = m₁ + 4 := by rw [hm₁]; ring)
    rw [hbody, Bootstrapping.Semiformula.imp_def, Bootstrapping.Semiformula.val_or]
    exact lift_lvB (conn_le (tag := 5) (le_trans hm₁2 le_self_add) (by norm_num) lnc lin)
      (le_of_add_eq (y := 152) (by rw [hm₁]; ring))
  have hstrip : sβ (100 * u + 300 + 3 * ((a + a : ℕ) : V)) + 1 ≤ W₂ + 1 + 1 := by
    have h3n : 3 * ((a + a : ℕ) : V) ≤ 18 := by
      have := mul_le_mul_of_nonneg_left hnV (show (0 : V) ≤ 3 by norm_num)
      exact this.trans (le_of_eq (by norm_num))
    calc sβ (100 * u + 300 + 3 * ((a + a : ℕ) : V)) + 1 ≤ sβ (100 * u + 300 + 18) + 1 := by
          unfold sβ
          exact _root_.add_le_add (_root_.add_le_add (mul_le_mul_of_nonneg_left
            (_root_.add_le_add (_root_.add_le_add le_rfl h3n) le_rfl) (by norm_num)) le_rfl) le_rfl
      _ ≤ sW (mBig u) :=
          le_of_add_eq (y := (symmD : V) + 100 * symmN + 4377) (by unfold sβ sW mBig; ring)
      _ ≤ lW₁ u := hsW
      _ ≤ W₂ + 1 + 1 := le_trans hW₂1 (le_trans le_self_add le_self_add)
  have D6 := strip (a + a) body (100 * u + 300) (W₂ + 1 + 1) hn6
    (le_trans hu (le_trans (le_mul_of_one_le_left (Arithmetic.zero_le _) (by norm_num)) le_self_add))
    lbody (le_trans hW₁4 (le_trans hW₂1 (le_trans le_self_add le_self_add))) hstrip
    (by rw [hshape]; exact D5)
  have hcf : SetCongruence.congruenceFormula a K = ∀⁰* body := rfl
  rw [hcf]
  refine D6.mono ?_
  have h15 : 15 * (a : V) ≤ 45 := by
    have := mul_le_mul_of_nonneg_left haV (show (0 : V) ≤ 15 by norm_num)
    exact this.trans (le_of_eq (by norm_num))
  unfold congL
  calc W₂ + 1 + 1 + 2 * ((a + a : ℕ) : V) = lW₁ u + (15 * (a : V) + 2) := by
        rw [hW₂]; push_cast; ring
    _ ≤ lW₁ u + 47 := _root_.add_le_add le_rfl (le_trans (_root_.add_le_add h15 le_rfl)
        (le_of_eq (by norm_num)))

end LeanProofs.ZFCinPA.SizedPlaceholderCongruence
