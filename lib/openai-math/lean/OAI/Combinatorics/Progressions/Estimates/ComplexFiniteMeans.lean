-- Modified for ProveIt: added `import OAI.Compat.*` lines (backported names); see lib/openai-math/README.md.
import Mathlib.Algebra.BigOperators.Ring.Finset
import OAI.Combinatorics.Progressions.Results.Basic
import OAI.Compat.BigOperators

namespace OAI

section

open scoped BigOperators

namespace Erdos3

theorem expect_fin_cons {G M : Type*} [Fintype G] [AddCommMonoid M] [Module ℚ≥0 M]
    {n : ℕ} (F : (Fin (n + 1) → G) → M) :
    (𝔼 x, F x) = 𝔼 a : G, 𝔼 y : Fin n → G, F (Fin.cons a y) := by
  calc
    (𝔼 x, F x) = 𝔼 p : G × (Fin n → G), F (Fin.cons p.1 p.2) := by
      apply Fintype.expect_equiv (Fin.consEquiv (fun _ : Fin (n + 1) ↦ G)).symm
      intro x
      congr 1
      simp
    _ = _ := by
      simpa using (Finset.expect_product' (Finset.univ : Finset G)
        (Finset.univ : Finset (Fin n → G)) (fun a y ↦ F (Fin.cons a y)))

theorem norm_expect_mul_star_sq_le {Ω : Type*} [Fintype Ω] (f g : Ω → ℂ) :
    ‖𝔼 x, f x * star (g x)‖ ^ 2 ≤
      (𝔼 x, ‖f x‖ ^ 2) * (𝔼 x, ‖g x‖ ^ 2) := by
  have hnorm : ‖𝔼 x, f x * star (g x)‖ ≤ 𝔼 x, ‖f x‖ * ‖g x‖ := by
    simpa only [norm_mul, norm_star] using
      (RCLike.norm_expect_le (K := ℂ) (f := fun x ↦ f x * star (g x)))
  exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans
    (Finset.expect_mul_sq_le_sq_mul_sq Finset.univ (fun x ↦ ‖f x‖) (fun x ↦ ‖g x‖))

theorem expect_square_le {Ω : Type*} [Fintype Ω] [Nonempty Ω] (f : Ω → ℝ) :
    (𝔼 x, f x) ^ 2 ≤ 𝔼 x, f x ^ 2 := by
  have h := Finset.expect_mul_sq_le_sq_mul_sq Finset.univ f (fun _ : Ω ↦ (1 : ℝ))
  simpa using h

theorem prod_bool_tuple_succ {M : Type*} [CommMonoid M] {n : ℕ}
    (F : (Fin (n + 1) → Bool) → M) :
    (∏ ω, F ω) =
      (∏ ω : Fin n → Bool, F (Fin.cons false ω)) *
        (∏ ω : Fin n → Bool, F (Fin.cons true ω)) := by
  calc
    (∏ ω, F ω) = ∏ q : Bool × (Fin n → Bool), F (Fin.cons q.1 q.2) := by
      apply Fintype.prod_equiv (Fin.consEquiv (fun _ : Fin (n + 1) ↦ Bool)).symm
      intro ω
      simp
    _ = _ := by rw [Fintype.prod_prod_type]; simp [mul_comm]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def orderedProductTail {n : ℕ} (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∏ j, if i < j then x j else 1

theorem orderedProductTail_zero {n : ℕ} (x : Fin (n + 1) → ℝ) :
    orderedProductTail x 0 = ∏ j : Fin n, x j.succ := by
  simp [orderedProductTail, Fin.prod_univ_succ]

theorem orderedProductTail_succ {n : ℕ} (x : Fin (n + 1) → ℝ) (i : Fin n) :
    orderedProductTail x i.succ = orderedProductTail (fun j => x j.succ) i := by
  simp [orderedProductTail, Fin.prod_univ_succ]

theorem orderedProduct_telescope (n : ℕ) (x : Fin n → ℝ) (c : ℝ) :
    (∏ i, x i) - c ^ n = ∑ i, c ^ i.val * (x i - c) * orderedProductTail x i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.prod_univ_succ, Fin.sum_univ_succ, orderedProductTail_zero]
    simp only [Fin.val_zero, pow_zero, one_mul]
    have hsum : (∑ i : Fin n, c ^ i.succ.val * (x i.succ - c) * orderedProductTail x i.succ) =
        c * (∑ i : Fin n, c ^ i.val * (x i.succ - c) * orderedProductTail (fun j => x j.succ) i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [orderedProductTail_succ, Fin.val_succ, pow_succ]
      ring
    rw [hsum, ← ih (fun j => x j.succ), pow_succ]
    ring

noncomputable def axisProduct {G : Type*} [Add G] {n : ℕ}
    (f : Fin n → G → ℝ) (t : Fin n → G) (y : G) : ℝ := ∏ i, f i (y + t i)

noncomputable def axisSuffix {G : Type*} [Add G] {n : ℕ}
    (f : Fin n → G → ℝ) (t : Fin n → G) (i : Fin n) (y : G) : ℝ :=
  orderedProductTail (fun j => f j (y + t j)) i

theorem axisSuffix_update {G : Type*} [Add G] {n : ℕ}
    (f : Fin n → G → ℝ) (t : Fin n → G) (i : Fin n) (a y : G) :
    axisSuffix f (Function.update t i a) i y = axisSuffix f t i y := by
  classical
  unfold axisSuffix orderedProductTail
  apply Finset.prod_congr rfl
  intro j _
  by_cases hij : i < j
  · simp only [hij, ite_true, Function.update_of_ne (ne_of_gt hij)]
  · simp only [hij, ite_false]

theorem axisProduct_nonneg {G : Type*} [Add G] {n : ℕ}
    (f : Fin n → G → ℝ) (hf : ∀ i y, 0 ≤ f i y) (t : Fin n → G) (y : G) :
    0 ≤ axisProduct f t y := Finset.prod_nonneg (fun i _ => hf i _)

theorem axisSuffix_nonneg {G : Type*} [Add G] {n : ℕ}
    (f : Fin n → G → ℝ) (hf : ∀ i y, 0 ≤ f i y) (t : Fin n → G) (i : Fin n) (y : G) :
    0 ≤ axisSuffix f t i y := by
  unfold axisSuffix orderedProductTail
  apply Finset.prod_nonneg
  intro j _
  split_ifs
  · exact hf j _
  · exact zero_le_one

theorem axisProduct_le_exp {G : Type*} [Add G] {n : ℕ} {p : ℝ}
    (f : Fin n → G → ℝ) (hf : ∀ i y, 0 ≤ f i y ∧ f i y ≤ Real.exp p)
    (t : Fin n → G) (y : G) : axisProduct f t y ≤ Real.exp ((n : ℝ) * p) := by
  calc
    _ ≤ ∏ _i : Fin n, Real.exp p :=
      Finset.prod_le_prod₀ (fun index _ => (hf index _).1) (fun index _ => (hf index _).2)
    _ = _ := by simp [Real.exp_nat_mul]

theorem axisSuffix_le_exp {G : Type*} [Add G] {n : ℕ} {p : ℝ} (hp : 0 ≤ p)
    (f : Fin n → G → ℝ) (hf : ∀ i y, 0 ≤ f i y ∧ f i y ≤ Real.exp p)
    (t : Fin n → G) (i : Fin n) (y : G) : axisSuffix f t i y ≤ Real.exp ((n : ℝ) * p) := by
  have h1 : 1 ≤ Real.exp p := Real.one_le_exp_iff.mpr hp
  calc
    _ ≤ ∏ _j : Fin n, Real.exp p := by
      unfold axisSuffix orderedProductTail
      apply Finset.prod_le_prod₀
      · intro j _
        split_ifs
        · exact (hf j _).1
        · exact zero_le_one
      · intro j _
        split_ifs
        · exact (hf j _).2
        · exact h1
    _ = _ := by simp [Real.exp_nat_mul]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

noncomputable def realShiftCorrelation (a J : G → ℝ) (h : G) : ℝ :=
  𝔼 n, a n * J (n + h)

noncomputable def realBilinearAverage (a H W : G → ℝ) : ℝ :=
  𝔼 x, 𝔼 y, H x * W y * a (x + y)

theorem bilinear_shift_identity (a J : G → ℝ) (E : Finset G) (c : ℝ) :
    realBilinearAverage a (fun x => c * J x) (fun y => if -y ∈ E then 1 else 0) =
      c * (𝔼 h, if h ∈ E then realShiftCorrelation a J h else 0) := by
  have hy (x : G) :
      (𝔼 y, (c * J x) * (if -y ∈ E then 1 else 0) * a (x + y)) =
        c * (𝔼 h, if h ∈ E then J x * a (x - h) else 0) := by
    calc
      _ = 𝔼 h, (c * J x) * (if h ∈ E then 1 else 0) * a (x - h) := by
        apply Fintype.expect_equiv (Equiv.neg G)
        intro y
        simp
      _ = _ := by
        rw [Finset.mul_expect]
        apply Finset.expect_congr rfl
        intro h _
        by_cases hh : h ∈ E <;> simp [hh, mul_assoc]
  unfold realBilinearAverage
  simp_rw [hy]
  rw [← Finset.mul_expect, Finset.expect_comm]
  congr 1
  apply Finset.expect_congr rfl
  intro h _
  by_cases hh : h ∈ E
  · simp only [hh, ite_true, realShiftCorrelation]
    symm
    apply Fintype.expect_equiv (Equiv.addRight h)
    intro n
    simp [mul_comm]
  · simp [hh]

theorem bilinear_bound_bad_shift_density (a J : G → ℝ) {M δ ε : ℝ}
    (hM : 0 < M) (hδ : 0 < δ)
    (hJ : ∀ x, 0 ≤ J x ∧ J x ≤ M)
    (hbilinear : ∀ H W : G → ℝ, (∀ x, 0 ≤ H x ∧ H x ≤ 1) →
      (∀ x, 0 ≤ W x ∧ W x ≤ 1) → realBilinearAverage a H W ≤ ε) :
    let E := Finset.univ.filter (fun h => δ < realShiftCorrelation a J h)
    (E.card : ℝ) / Fintype.card G ≤ M * ε / δ := by
  classical
  intro E
  let H : G → ℝ := fun x => M⁻¹ * J x
  let W : G → ℝ := fun y => if -y ∈ E then 1 else 0
  have hH : ∀ x, 0 ≤ H x ∧ H x ≤ 1 := by
    intro x
    constructor
    · exact mul_nonneg (inv_nonneg.mpr hM.le) (hJ x).1
    · dsimp [H]
      calc
        M⁻¹ * J x ≤ M⁻¹ * M := mul_le_mul_of_nonneg_left (hJ x).2 (inv_nonneg.mpr hM.le)
        _ = 1 := inv_mul_cancel₀ hM.ne'
  have hW : ∀ x, 0 ≤ W x ∧ W x ≤ 1 := by
    intro x
    dsimp [W]
    split_ifs <;> norm_num
  have hb := hbilinear H W hH hW
  rw [bilinear_shift_identity] at hb
  have hsum : (E.card : ℝ) * δ ≤ ∑ h ∈ E, realShiftCorrelation a J h := by
    calc
      _ = ∑ _h ∈ E, δ := by simp
      _ ≤ _ := Finset.sum_le_sum (fun h hh => (Finset.mem_filter.mp hh).2.le)
  have hcard : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hlower : δ * ((E.card : ℝ) / Fintype.card G) ≤
      𝔼 h, if h ∈ E then realShiftCorrelation a J h else 0 := by
    rw [Fintype.expect_eq_sum_div_card]
    simp only [Finset.sum_ite_mem, Finset.univ_inter]
    have := div_le_div_of_nonneg_right hsum hcard.le
    simpa only [mul_div_assoc, mul_comm] using this
  have hupper : (𝔼 h, if h ∈ E then realShiftCorrelation a J h else 0) ≤ M * ε := by
    have h := mul_le_mul_of_nonneg_left hb hM.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hM.ne', one_mul] using h
  exact (le_div_iff₀ hδ).mpr (by simpa only [mul_comm] using hlower.trans hupper)

theorem exists_small_bad_shift_set (a J : G → ℝ) {p : ℝ} (hp : 0 ≤ p)
    (hJ : ∀ x, 0 ≤ J x ∧ J x ≤ Real.exp p)
    (hbilinear : ∀ H W : G → ℝ, (∀ x, 0 ≤ H x ∧ H x ≤ 1) →
      (∀ x, 0 ≤ W x ∧ W x ≤ 1) → realBilinearAverage a H W ≤ Real.exp (-4 * p)) :
    ∃ E : Finset G, (E.card : ℝ) ≤ Real.exp (-p) * Fintype.card G ∧
      ∀ h ∉ E, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        realShiftCorrelation a J h * t ≤ Real.exp (-p) := by
  classical
  let E := Finset.univ.filter (fun h => Real.exp (-p) < realShiftCorrelation a J h)
  have h := bilinear_bound_bad_shift_density a J (Real.exp_pos p) (Real.exp_pos (-p)) hJ hbilinear
  change (E.card : ℝ) / Fintype.card G ≤ _ at h
  have hexp : Real.exp p * Real.exp (-4 * p) / Real.exp (-p) ≤ Real.exp (-p) := by
    rw [← Real.exp_add, ← Real.exp_sub]
    apply Real.exp_le_exp.mpr
    linarith
  have hcard : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  refine ⟨E, (div_le_iff₀ hcard).mp (h.trans hexp), ?_⟩
  intro k hk t ht ht1
  have hk' : realShiftCorrelation a J k ≤ Real.exp (-p) := by
    simpa only [E, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] using hk
  exact (mul_le_mul_of_nonneg_right hk' ht).trans
    (mul_le_of_le_one_right (Real.exp_nonneg _) ht1)

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

theorem expect_prod_boolean_pow_le {Ω : Type*} [Fintype Ω]
    (n : ℕ) (F : (Fin n → Bool) → Ω → ℝ) (hF : ∀ ω x, 0 ≤ F ω x) :
    (𝔼 x, ∏ ω, F ω x) ^ (2 ^ n) ≤ ∏ ω, 𝔼 x, F ω x ^ (2 ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    let A (b : Bool) (x : Ω) := ∏ ω : Fin n → Bool, F (Fin.cons b ω) x
    have hprod (x : Ω) : (∏ ω, F ω x) = A false x * A true x :=
      prod_bool_tuple_succ _
    have hcs := Finset.expect_mul_sq_le_sq_mul_sq Finset.univ (A false) (A true)
    have hpart (b : Bool) : (𝔼 x, A b x ^ 2) ^ (2 ^ n) ≤
        ∏ ω : Fin n → Bool, 𝔼 x, F (Fin.cons b ω) x ^ (2 ^ (n + 1)) := by
      have h := ih (fun ω x ↦ F (Fin.cons b ω) x ^ 2) (fun _ _ ↦ sq_nonneg _)
      simpa only [A, ← Finset.prod_pow, ← pow_mul, ← pow_succ'] using h
    calc
      (𝔼 x, ∏ ω, F ω x) ^ (2 ^ (n + 1)) =
          ((𝔼 x, A false x * A true x) ^ 2) ^ (2 ^ n) := by
        simp_rw [hprod]
        rw [← pow_mul, pow_succ']
      _ ≤ ((𝔼 x, A false x ^ 2) * (𝔼 x, A true x ^ 2)) ^ (2 ^ n) :=
        pow_le_pow_left₀ (sq_nonneg _) hcs _
      _ = (𝔼 x, A false x ^ 2) ^ (2 ^ n) * (𝔼 x, A true x ^ 2) ^ (2 ^ n) :=
        mul_pow _ _ _
      _ ≤ (∏ ω : Fin n → Bool, 𝔼 x, F (Fin.cons false ω) x ^ (2 ^ (n + 1))) *
          (∏ ω : Fin n → Bool, 𝔼 x, F (Fin.cons true ω) x ^ (2 ^ (n + 1))) := by
        apply mul_le_mul (hpart false) (hpart true)
        · exact pow_nonneg (Finset.expect_nonneg (fun _ _ ↦ sq_nonneg _)) _
        · exact Finset.prod_nonneg (fun ω _ ↦ Finset.expect_nonneg
            (fun x _ ↦ pow_nonneg (hF _ x) _))
      _ = ∏ ω, 𝔼 x, F ω x ^ (2 ^ (n + 1)) :=
        (prod_bool_tuple_succ (fun ω ↦ 𝔼 x, F ω x ^ (2 ^ (n + 1)))).symm

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*}

noncomputable def cellAverage [Add G] (C : Finset G) (f : G → ℝ) (x : G) : ℝ :=
  𝔼 c ∈ C, f (x + c)

theorem cellAverage_nonneg [Add G] (C : Finset G) (f : G → ℝ)
    (hf : ∀ x, 0 ≤ f x) (x : G) : 0 ≤ cellAverage C f x :=
  Finset.expect_nonneg (fun c _ => hf (x + c))

theorem cellAverage_le [Add G] {C : Finset G} (hC : C.Nonempty) (f : G → ℝ)
    {M : ℝ} (hf : ∀ x, f x ≤ M) (x : G) : cellAverage C f x ≤ M :=
  (Finset.expect_le_expect (fun c (_ : c ∈ C) => hf (x + c))).trans_eq (Finset.expect_const hC M)

variable [Fintype G] [DecidableEq G]

theorem expect_comp_le_expect_of_support (L : Finset G) (f : G → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hsupport : ∀ x, x ∉ L → f x = 0)
    (phi : G → G) (hphi : Function.Injective phi) :
    (𝔼 x ∈ L, f (phi x)) ≤ 𝔼 x ∈ L, f x := by
  have hsum : (∑ x ∈ L, f (phi x)) ≤ ∑ x, f x := by
    rw [← Finset.sum_image hphi.injOn]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun x _ _ => hf x)
  have htotal : (∑ x ∈ L, f x) = ∑ x, f x :=
    Finset.sum_subset (Finset.subset_univ L) (fun x _ hx => hsupport x hx)
  simp only [Finset.expect_eq_sum_div_card]
  rw [htotal]
  exact div_le_div_of_nonneg_right hsum (Nat.cast_nonneg L.card)

variable [AddCommGroup G]

theorem expect_cellAverage_comp_le (L C : Finset G) (hC : C.Nonempty) (f : G → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hsupport : ∀ x, x ∉ L → f x = 0)
    (phi : G → G) (hphi : Function.Injective phi) :
    (𝔼 x ∈ L, cellAverage C f (phi x)) ≤ 𝔼 x ∈ L, f x := by
  unfold cellAverage
  rw [Finset.expect_comm]
  have h := Finset.expect_le_expect (fun c (_ : c ∈ C) =>
    expect_comp_le_expect_of_support L f hf hsupport (fun x => phi x + c)
      (fun _ _ h => hphi (add_right_cancel h)))
  simpa only [Finset.expect_const hC] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem centered_product_mean_expansion {I X : Type*} [DecidableEq I] [Fintype X]
    (S : Finset I) (hS : S.Nonempty) (F : I → X → ℝ) :
    (𝔼 x, ∏ i ∈ S, (F i x - 1)) =
      ∑ U ∈ S.powerset, (-1 : ℝ) ^ U.card * ((𝔼 x, ∏ i ∈ S \ U, F i x) - 1) := by
  have hpoint (x : X) : (∏ i ∈ S, (F i x - 1)) =
      ∑ U ∈ S.powerset, (-1 : ℝ) ^ U.card * (∏ i ∈ S \ U, F i x) := by
    simpa only [Finset.prod_const_one, mul_one] using
      Finset.prod_sub (fun i => F i x) (fun _ => (1 : ℝ)) S
  have hzero : (∑ U ∈ S.powerset, (-1 : ℝ) ^ U.card) = 0 := by
    have h := (Finset.prod_sub (fun _ : I => (1 : ℝ)) (fun _ => (1 : ℝ)) S).symm
    simpa [hS.ne_empty] using h
  simp only [hpoint, Finset.expect_sum_comm, ← Finset.mul_expect]
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hzero, sub_zero]

theorem centered_product_mean_abs_le {I X : Type*} [DecidableEq I] [Fintype X]
    (S : Finset I) (hS : S.Nonempty) (F : I → X → ℝ) {error : ℝ}
    (hmean : ∀ U ⊆ S, |(𝔼 x, ∏ i ∈ U, F i x) - 1| ≤ error) :
    |𝔼 x, ∏ i ∈ S, (F i x - 1)| ≤ (2 : ℝ) ^ S.card * error := by
  rw [centered_product_mean_expansion S hS F]
  calc
    _ ≤ ∑ U ∈ S.powerset,
        |(-1 : ℝ) ^ U.card * ((𝔼 x, ∏ i ∈ S \ U, F i x) - 1)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _U ∈ S.powerset, error := by
      apply Finset.sum_le_sum
      intro U _
      simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      exact hmean (S \ U) Finset.sdiff_subset
    _ = _ := by simp

theorem absolute_centered_product_mean_le {I X : Type*} [DecidableEq I] [Fintype X]
    (S : Finset I) (F : I → X → ℝ) {A : ℝ}
    (hF : ∀ i ∈ S, ∀ x, 0 ≤ F i x)
    (hmean : ∀ U ⊆ S, (𝔼 x, ∏ i ∈ U, F i x) ≤ A) :
    (𝔼 x, ∏ i ∈ S, |F i x - 1|) ≤ (2 : ℝ) ^ S.card * A := by
  calc
    _ ≤ 𝔼 x, ∏ i ∈ S, (F i x + 1) := by
      apply Finset.expect_le_expect
      intro x _
      apply Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
      intro i hi
      exact abs_le.mpr ⟨by linarith [hF i hi x], by linarith⟩
    _ = ∑ U ∈ S.powerset, 𝔼 x, ∏ i ∈ U, F i x := by
      simp only [Finset.prod_add_one, Finset.expect_sum_comm]
    _ ≤ ∑ _U ∈ S.powerset, A := by
      apply Finset.sum_le_sum
      intro U hU
      exact hmean U (Finset.mem_powerset.mp hU)
    _ = _ := by simp

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_common_slice_of_equal_marginals {A B H : Type*}
    [Fintype A] [Fintype B] [Fintype H] [Nonempty A] [Nonempty B] [Nonempty H]
    (f : A → H → ℝ) (g : B → H → ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hmarginal : ∀ h, (𝔼 a, f a h) = 𝔼 b, g b h)
    (hmean : δ ≤ 𝔼 h, 𝔼 a, f a h) :
    ∃ (a : A) (b : B), δ ^ 2 ≤ 𝔼 h, f a h * g b h := by
  have henergy := (pow_le_pow_left₀ hδ hmean 2).trans
    (expect_square_le (fun h => 𝔼 a, f a h))
  have hproduct : (𝔼 h, (𝔼 a, f a h) ^ 2) = 𝔼 a, 𝔼 b, 𝔼 h, f a h * g b h := by
    calc
      _ = 𝔼 h, (𝔼 a, f a h) * (𝔼 b, g b h) := by
        apply Finset.expect_congr rfl
        intro h _
        rw [← hmarginal h, pow_two]
      _ = 𝔼 h, 𝔼 a, 𝔼 b, f a h * g b h := by simp_rw [Fintype.expect_mul_expect]
      _ = 𝔼 a, 𝔼 h, 𝔼 b, f a h * g b h := Finset.expect_comm _ _ _
      _ = _ := by
        apply Finset.expect_congr rfl
        intro a _
        exact Finset.expect_comm _ _ _
  obtain ⟨a, _, ha⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty (henergy.trans_eq hproduct)
  obtain ⟨b, _, hb⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty ha
  exact ⟨a, b, hb⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem complex_ofReal_expect {X : Type*} [Fintype X] (f : X → ℝ) :
    (((𝔼 x, f x) : ℝ) : ℂ) = 𝔼 x, (f x : ℂ) := by
  simp only [Fintype.expect_eq_sum_div_card, Complex.ofReal_div, Complex.ofReal_sum,
    Complex.ofReal_natCast]

theorem real_mean_le_of_complex_mean_close {X : Type*} [Fintype X]
    (f : X → ℝ) {epsilon : ℝ} (h : ‖(𝔼 x, (f x : ℂ)) - 1‖ ≤ epsilon) :
    (𝔼 x, f x) ≤ 1 + epsilon := by
  rw [← complex_ofReal_expect, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] at h
  linarith [(abs_le.mp h).2]

end Erdos3

end

end OAI
