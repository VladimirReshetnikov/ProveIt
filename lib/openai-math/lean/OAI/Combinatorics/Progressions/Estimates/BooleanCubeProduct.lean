-- Modified for ProveIt: added `import OAI.Compat.*` lines (backported names); see lib/openai-math/README.md.
import OAI.Combinatorics.Progressions.Estimates.DenseCorrelationPairs
import OAI.Compat.Core
import OAI.Compat.BigOperators

namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H]

noncomputable def mixedGowersMoment : (j : ℕ) → ((Fin j → Bool) → H → ℂ) → ℂ
  | 0, F => 𝔼 x, F default x
  | j + 1, F => 𝔼 h, mixedGowersMoment j
      (fun ω ↦ crossDerivative (F (Fin.cons false ω)) (F (Fin.cons true ω)) h)

theorem mixedGowersMoment_const (j : ℕ) (f : H → ℂ) :
    mixedGowersMoment j (fun _ ↦ f) = gowersMoment j f := by
  induction j generalizing f with
  | zero => rfl
  | succ j ih => simp only [mixedGowersMoment, crossDerivative_self, ih, gowersMoment]

theorem mixedGowersMoment_one (F : (Fin 1 → Bool) → H → ℂ) :
    mixedGowersMoment 1 F =
      (𝔼 x, F (Fin.cons false default) x) * star (𝔼 x, F (Fin.cons true default) x) :=
  expect_crossDerivative _ _

theorem norm_mixedGowersMoment_le (j : ℕ) (F : (Fin (j + 1) → Bool) → H → ℂ) :
    ‖mixedGowersMoment (j + 1) F‖ ≤ ∏ ω, gowersNorm (j + 1) (F ω) := by
  induction j with
  | zero =>
    rw [mixedGowersMoment_one, norm_mul, norm_star, prod_bool_tuple_succ]
    rw [Fintype.prod_subsingleton _ (default : Fin 0 → Bool),
      Fintype.prod_subsingleton _ (default : Fin 0 → Bool),
      gowersNorm_one, gowersNorm_one]
  | succ j ih =>
    let D (ω : Fin (j + 1) → Bool) (h : H) :=
      crossDerivative (F (Fin.cons false ω)) (F (Fin.cons true ω)) h
    have hnorm : ‖mixedGowersMoment (j + 2) F‖ ≤
        𝔼 h, ∏ ω, gowersNorm (j + 1) (D ω h) := by
      change ‖𝔼 h, mixedGowersMoment (j + 1) (fun ω ↦ D ω h)‖ ≤ _
      exact (RCLike.norm_expect_le (K := ℂ)).trans
        (Finset.expect_le_expect (fun h _ ↦ ih (fun ω ↦ D ω h)))
    have hholder := expect_prod_boolean_pow_le (j + 1)
      (fun ω h ↦ gowersNorm (j + 1) (D ω h)) (fun ω h ↦ gowersNorm_nonneg j _)
    have hcross : (∏ ω, 𝔼 h, gowersNorm (j + 1) (D ω h) ^ (2 ^ (j + 1))) ≤
        ∏ ω : Fin (j + 1) → Bool,
          (gowersNorm (j + 2) (F (Fin.cons false ω)) *
            gowersNorm (j + 2) (F (Fin.cons true ω))) ^ (2 ^ (j + 1)) := by
      apply Finset.prod_le_prod₀
      · intro ω hω
        exact Finset.expect_nonneg (fun h _ ↦ pow_nonneg (gowersNorm_nonneg j _) _)
      · intro ω hω
        exact expect_cross_gowersNorm_pow_le j _ _
    have hfactor : (∏ ω : Fin (j + 1) → Bool,
          (gowersNorm (j + 2) (F (Fin.cons false ω)) *
            gowersNorm (j + 2) (F (Fin.cons true ω))) ^ (2 ^ (j + 1))) =
        (∏ ω, gowersNorm (j + 2) (F ω)) ^ (2 ^ (j + 1)) := by
      rw [Finset.prod_pow, Finset.prod_mul_distrib,
        ← prod_bool_tuple_succ (fun ω ↦ gowersNorm (j + 2) (F ω))]
    apply le_of_pow_le_pow_left₀ (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0))
      (Finset.prod_nonneg (fun ω _ ↦ gowersNorm_nonneg (j + 1) _))
    exact (pow_le_pow_left₀ (norm_nonneg _) hnorm _).trans
      (hholder.trans (hcross.trans_eq hfactor))

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

def booleanWeight {j : ℕ} (ω : Fin j → Bool) : ℕ :=
  ∑ i, if ω i then 1 else 0

@[simp] theorem booleanWeight_cons_false {j : ℕ} (ω : Fin j → Bool) :
    booleanWeight (Fin.cons false ω) = booleanWeight ω := by
  unfold booleanWeight
  rw [Fin.sum_univ_succ]
  simp

@[simp] theorem booleanWeight_cons_true {j : ℕ} (ω : Fin j → Bool) :
    booleanWeight (Fin.cons true ω) = booleanWeight ω + 1 := by
  unfold booleanWeight
  rw [Fin.sum_univ_succ]
  simp [Nat.add_comm]

variable {H : Type*} [AddCommGroup H]

def cubeShift {j : ℕ} (hs : Fin j → H) (ω : Fin j → Bool) : H :=
  ∑ i, if ω i then hs i else 0

@[simp] theorem cubeShift_cons_false {j : ℕ} (h : H) (hs : Fin j → H)
    (ω : Fin j → Bool) : cubeShift (Fin.cons h hs) (Fin.cons false ω) = cubeShift hs ω := by
  simp [cubeShift, Fin.sum_univ_succ]

@[simp] theorem cubeShift_cons_true {j : ℕ} (h : H) (hs : Fin j → H)
    (ω : Fin j → Bool) : cubeShift (Fin.cons h hs) (Fin.cons true ω) = h + cubeShift hs ω := by
  simp [cubeShift, Fin.sum_univ_succ]

def mixedCubeProduct {j : ℕ} (F : (Fin j → Bool) → H → ℂ) (hs : Fin j → H) (x : H) : ℂ :=
  ∏ ω, conjugationPower (booleanWeight ω) (F ω (x + cubeShift hs ω))

@[simp] theorem mixedCubeProduct_zero (F : (Fin 0 → Bool) → H → ℂ)
    (hs : Fin 0 → H) (x : H) : mixedCubeProduct F hs x = F default x := by
  unfold mixedCubeProduct
  rw [Fintype.prod_subsingleton _ (default : Fin 0 → Bool)]
  simp [booleanWeight, cubeShift, conjugationPower]

theorem mixedCubeProduct_cons {j : ℕ} (F : (Fin (j + 1) → Bool) → H → ℂ)
    (h : H) (hs : Fin j → H) (x : H) :
    mixedCubeProduct F (Fin.cons h hs) x =
      mixedCubeProduct (fun ω ↦ F (Fin.cons false ω)) hs x *
        star (mixedCubeProduct (fun ω ↦ F (Fin.cons true ω)) hs (x + h)) := by
  simp only [mixedCubeProduct]
  rw [prod_bool_tuple_succ]
  simp only [booleanWeight_cons_false, booleanWeight_cons_true,
    cubeShift_cons_false, cubeShift_cons_true, conjugationPower, RingHom.comp_apply,
    starRingEnd_apply, ← add_assoc]
  change _ = _ * (starRingEnd ℂ) _
  rw [map_prod]
  simp only [starRingEnd_apply]

theorem mixedCubeProduct_crossDerivative {j : ℕ} (F G : (Fin j → Bool) → H → ℂ)
    (h : H) (hs : Fin j → H) (x : H) :
    mixedCubeProduct (fun ω ↦ crossDerivative (F ω) (G ω) h) hs x =
      mixedCubeProduct F hs x * star (mixedCubeProduct G hs (x + h)) := by
  simp only [mixedCubeProduct, crossDerivative, map_mul, conjugationPower_star,
    Finset.prod_mul_distrib]
  change _ = _ * (starRingEnd ℂ) _
  rw [map_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro ω hω
  congr 3
  abel

variable [Fintype H]

theorem mixedGowersMoment_eq_expect_cube {j : ℕ} (F : (Fin j → Bool) → H → ℂ) :
    mixedGowersMoment j F = 𝔼 hs : Fin j → H, 𝔼 x, mixedCubeProduct F hs x := by
  induction j with
  | zero => simp [mixedGowersMoment]
  | succ j ih =>
    rw [mixedGowersMoment, expect_fin_cons]
    simp_rw [ih, mixedCubeProduct_crossDerivative, mixedCubeProduct_cons]

theorem mixedGowersMoment_sum {j : ℕ} {κ : (Fin j → Bool) → Type*}
    [∀ ω, Fintype (κ ω)] (F : ∀ ω, κ ω → H → ℂ) :
    mixedGowersMoment j (fun ω x ↦ ∑ k, F ω k x) =
      ∑ q : ∀ ω, κ ω, mixedGowersMoment j (fun ω ↦ F ω (q ω)) := by
  classical
  simp only [mixedGowersMoment_eq_expect_cube, mixedCubeProduct, map_sum,
    Fintype.prod_sum, Finset.expect_sum_comm]

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H]

theorem norm_gowersMoment (j : ℕ) (f : H → ℂ) :
    ‖gowersMoment (j + 1) f‖ = (gowersMoment (j + 1) f).re := by
  have he : gowersMoment (j + 1) f = ((gowersMoment (j + 1) f).re : ℂ) := by
    apply Complex.ext
    · rfl
    · simp only [gowersMoment_im_zero, Complex.ofReal_im]
  conv_lhs => rw [he]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (gowersMoment_re_nonneg j f)]

theorem gowersNorm_sum {ι : Type*} [Fintype ι] (j : ℕ) (f : ι → H → ℂ) :
    gowersNorm (j + 1) (fun x ↦ ∑ i, f i x) ≤ ∑ i, gowersNorm (j + 1) (f i) := by
  classical
  apply le_of_pow_le_pow_left₀ (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0))
    (Finset.sum_nonneg (fun i _ ↦ gowersNorm_nonneg j _))
  calc
    gowersNorm (j + 1) (fun x ↦ ∑ i, f i x) ^ (2 ^ (j + 1)) =
        ‖mixedGowersMoment (j + 1) (fun _ x ↦ ∑ i, f i x)‖ := by
      rw [mixedGowersMoment_const, norm_gowersMoment, gowersNorm_pow]
    _ = ‖∑ q : (Fin (j + 1) → Bool) → ι,
        mixedGowersMoment (j + 1) (fun ω ↦ f (q ω))‖ := by
      rw [mixedGowersMoment_sum (fun _ i ↦ f i)]
    _ ≤ ∑ q : (Fin (j + 1) → Bool) → ι,
        ‖mixedGowersMoment (j + 1) (fun ω ↦ f (q ω))‖ := norm_sum_le _ _
    _ ≤ ∑ q : (Fin (j + 1) → Bool) → ι,
        ∏ ω, gowersNorm (j + 1) (f (q ω)) :=
      Finset.sum_le_sum (fun q _ ↦ norm_mixedGowersMoment_le j _)
    _ = ∏ _ω : Fin (j + 1) → Bool, ∑ i, gowersNorm (j + 1) (f i) :=
      (Fintype.prod_sum (fun (_ω : Fin (j + 1) → Bool) i ↦
        gowersNorm (j + 1) (f i))).symm
    _ = (∑ i, gowersNorm (j + 1) (f i)) ^ (2 ^ (j + 1)) := by simp

theorem gowersNorm_add (j : ℕ) (f g : H → ℂ) :
    gowersNorm (j + 1) (fun x ↦ f x + g x) ≤
      gowersNorm (j + 1) f + gowersNorm (j + 1) g := by
  simpa [add_comm] using
    (gowersNorm_sum j (fun b : Bool ↦ if b then f else g))

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H]

theorem gowersMoment_translate (j : ℕ) (f : H → ℂ) (a : H) :
    gowersMoment j (fun x ↦ f (a + x)) = gowersMoment j f := by
  induction j generalizing f with
  | zero => exact expect_translate f a
  | succ j ih =>
    have hd (h : H) : multiplicativeDerivative (fun x ↦ f (a + x)) h =
        (fun x ↦ multiplicativeDerivative f h (a + x)) := by
      funext x
      simp only [multiplicativeDerivative, add_assoc]
    simp only [gowersMoment, hd, ih]

theorem gowersNorm_translate (j : ℕ) (f : H → ℂ) (a : H) :
    gowersNorm j (fun x ↦ f (a + x)) = gowersNorm j f := by
  simp only [gowersNorm, gowersMoment_translate]

omit [Fintype H] in
theorem multiplicativeDerivative_const_mul (c : ℂ) (f : H → ℂ) (h : H) :
    multiplicativeDerivative (fun x ↦ c * f x) h =
      (fun x ↦ (c * star c) * multiplicativeDerivative f h x) := by
  funext x
  simp only [multiplicativeDerivative, star_mul]
  ring

theorem gowersNorm_const_mul (j : ℕ) (c : ℂ) (f : H → ℂ) :
    gowersNorm (j + 1) (fun x ↦ c * f x) = ‖c‖ * gowersNorm (j + 1) f := by
  induction j generalizing c f with
  | zero =>
    simp only [Nat.zero_add, gowersNorm_one, ← Finset.mul_expect, norm_mul]
  | succ j ih =>
    apply (pow_left_inj₀ (gowersNorm_nonneg (j + 1) _)
      (mul_nonneg (norm_nonneg _) (gowersNorm_nonneg (j + 1) _))
      (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0))).mp
    rw [gowersNorm_derivative, mul_pow, gowersNorm_derivative]
    simp only [multiplicativeDerivative_const_mul, ih, norm_mul, norm_star, mul_pow]
    rw [← Finset.mul_expect]
    congr 1
    rw [← pow_add]
    congr 1
    simp [pow_succ, Nat.mul_two]

theorem gowersNorm_le_succ (j : ℕ) (f : H → ℂ) :
    gowersNorm (j + 1) f ≤ gowersNorm (j + 2) f := by
  let F (ω : Fin (j + 2) → Bool) : H → ℂ := if ω 0 then (fun _ ↦ 1) else f
  have hm : mixedGowersMoment (j + 2) F = gowersMoment (j + 1) f := by
    change (𝔼 h, mixedGowersMoment (j + 1)
      (fun ω ↦ crossDerivative (F (Fin.cons false ω)) (F (Fin.cons true ω)) h)) = _
    have hd (h : H) :
        (fun ω ↦ crossDerivative (F (Fin.cons false ω)) (F (Fin.cons true ω)) h) =
        (fun _ : Fin (j + 1) → Bool ↦ f) := by
      funext ω x
      simp [F, crossDerivative]
    simp only [hd, mixedGowersMoment_const, Fintype.expect_const]
  have hp : (∏ ω, gowersNorm (j + 2) (F ω)) = gowersNorm (j + 2) f ^ (2 ^ (j + 1)) := by
    rw [prod_bool_tuple_succ]
    simp [F, gowersNorm_const_one]
  apply le_of_pow_le_pow_left₀ (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0))
    (gowersNorm_nonneg (j + 1) f)
  rw [gowersNorm_pow, ← norm_gowersMoment, ← hm]
  exact (norm_mixedGowersMoment_le (j + 1) F).trans_eq hp

theorem norm_expect_le_gowersNorm (j : ℕ) (f : H → ℂ) :
    ‖𝔼 x, f x‖ ≤ gowersNorm (j + 1) f := by
  induction j with
  | zero => exact (gowersNorm_one f).ge
  | succ j ih => exact ih.trans (gowersNorm_le_succ j f)

theorem gowersNorm_mul_character (j : ℕ) (χ f : H → ℂ)
    (hχ : ∀ x y, χ (x + y) = χ x * χ y) (hunit : ∀ x, ‖χ x‖ = 1) :
    gowersNorm (j + 2) (fun x ↦ χ x * f x) = gowersNorm (j + 2) f := by
  have hcancel (x : H) : χ x * star (χ x) = 1 := by
    change χ x * (starRingEnd ℂ) (χ x) = 1
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hunit]
    norm_num
  have hd (h : H) : multiplicativeDerivative (fun x ↦ χ x * f x) h =
      (fun x ↦ star (χ h) * multiplicativeDerivative f h x) := by
    funext x
    simp only [multiplicativeDerivative, hχ, star_mul]
    calc
      _ =
          (χ x * star (χ x)) * (star (χ h) * (f x * star (f (x + h)))) := by ring
      _ = _ := by rw [hcancel, one_mul]
  apply (pow_left_inj₀ (gowersNorm_nonneg (j + 1) _)
    (gowersNorm_nonneg (j + 1) _)
    (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0))).mp
  rw [gowersNorm_derivative, gowersNorm_derivative]
  simp only [hd, gowersNorm_const_mul, norm_star, hunit, one_mul]

theorem gowersNorm_const (j : ℕ) (c : ℂ) :
    gowersNorm (j + 1) (fun _ : H ↦ c) = ‖c‖ := by
  simpa only [mul_one, gowersNorm_const_one] using
    (gowersNorm_const_mul j c (fun _ : H ↦ 1))

@[simp] theorem gowersNorm_zero (j : ℕ) :
    gowersNorm (j + 1) (fun _ : H ↦ 0) = 0 := by
  rw [gowersNorm_const, norm_zero]

theorem gowersNorm_neg (j : ℕ) (f : H → ℂ) :
    gowersNorm (j + 1) (fun x ↦ -f x) = gowersNorm (j + 1) f := by
  simpa using gowersNorm_const_mul j (-1) f

theorem gowersNorm_sub_le (j : ℕ) (f g : H → ℂ) :
    gowersNorm (j + 1) (fun x ↦ f x - g x) ≤
      gowersNorm (j + 1) f + gowersNorm (j + 1) g := by
  simpa only [sub_eq_add_neg, gowersNorm_neg] using gowersNorm_add j f (fun x ↦ -g x)

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H]

theorem norm_gowersMoment_le_mean_norm (j : ℕ) (f : H → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) : ‖gowersMoment j f‖ ≤ 𝔼 x, ‖f x‖ := by
  induction j generalizing f with
  | zero => exact RCLike.norm_expect_le (K := ℂ)
  | succ j ih =>
    have hunit (h x : H) : ‖multiplicativeDerivative f h x‖ ≤ 1 := by
      simpa only [multiplicativeDerivative, norm_mul, norm_star, one_mul] using
        mul_le_mul (hf x) (hf (x + h)) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    have hnorm (h x : H) : ‖multiplicativeDerivative f h x‖ ≤ ‖f x‖ := by
      simpa only [multiplicativeDerivative, norm_mul, norm_star, mul_one] using
        mul_le_mul_of_nonneg_left (hf (x + h)) (norm_nonneg (f x))
    calc
      _ ≤ 𝔼 h, ‖gowersMoment j (multiplicativeDerivative f h)‖ := RCLike.norm_expect_le (K := ℂ)
      _ ≤ 𝔼 _h : H, 𝔼 x, ‖f x‖ := by
        apply Finset.expect_le_expect
        intro h _
        exact (ih _ (hunit h)).trans (Finset.expect_le_expect (fun x _ => hnorm h x))
      _ = _ := Fintype.expect_const _

theorem gowersNorm_pow_le_mean_norm (j : ℕ) (f : H → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    gowersNorm (j + 1) f ^ (2 ^ (j + 1)) ≤ 𝔼 x, ‖f x‖ := by
  rw [gowersNorm_pow, ← norm_gowersMoment]
  exact norm_gowersMoment_le_mean_norm (j + 1) f hf

theorem gowersNorm_le_of_mean_norm_le_pow (j : ℕ) (f : H → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) {ε : ℝ} (hε : 0 ≤ ε)
    (hmean : (𝔼 x, ‖f x‖) ≤ ε ^ (2 ^ (j + 1))) : gowersNorm (j + 1) f ≤ ε := by
  exact le_of_pow_le_pow_left₀ (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0)) hε
    ((gowersNorm_pow_le_mean_norm j f hf).trans hmean)

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

def restrictTo (Q : Finset H) (f : H → ℂ) : H → ℂ :=
  fun x ↦ if x ∈ Q then f x else 0

omit [AddCommGroup H] [Fintype H] in
@[simp] theorem restrictTo_empty (f : H → ℂ) :
    restrictTo ∅ f = (fun _ ↦ 0) := by
  funext x
  simp [restrictTo]

omit [AddCommGroup H] in
theorem expect_restrictTo (Q : Finset H) (f : H → ℂ) :
    (𝔼 x, restrictTo Q f x) = (∑ x ∈ Q, f x) / Fintype.card H := by
  simp [restrictTo, Fintype.expect_eq_sum_div_card]

omit [AddCommGroup H] in
theorem norm_expect_restrict_one (Q : Finset H) :
    ‖𝔼 x, restrictTo Q (fun _ ↦ 1) x‖ = (Q.card : ℝ) / Fintype.card H := by
  rw [expect_restrictTo]
  simp

theorem gowersNorm_restrict_one_pos (j : ℕ) {Q : Finset H} (hQ : Q.Nonempty) :
    0 < gowersNorm (j + 1) (restrictTo Q (fun _ ↦ 1)) := by
  have hmean : 0 < ‖𝔼 x, restrictTo Q (fun _ ↦ 1) x‖ := by
    rw [norm_expect_restrict_one]
    exact div_pos (by exact_mod_cast hQ.card_pos)
      (by exact_mod_cast Fintype.card_pos)
  exact hmean.trans_le (norm_expect_le_gowersNorm j _)

noncomputable def restrictedGowersNorm (j : ℕ) (Q : Finset H) (f : H → ℂ) : ℝ :=
  gowersNorm j (restrictTo Q f) / gowersNorm j (restrictTo Q (fun _ ↦ 1))

theorem restrictedGowersNorm_nonneg (j : ℕ) (Q : Finset H) (f : H → ℂ) :
    0 ≤ restrictedGowersNorm (j + 1) Q f :=
  div_nonneg (gowersNorm_nonneg j _) (gowersNorm_nonneg j _)

theorem restrictedGowersNorm_one (j : ℕ) {Q : Finset H} (hQ : Q.Nonempty) :
    restrictedGowersNorm (j + 1) Q (fun _ ↦ 1) = 1 :=
  div_self (gowersNorm_restrict_one_pos j hQ).ne'

theorem restrictedGowersNorm_degree_one {Q : Finset H} (hQ : Q.Nonempty) (f : H → ℂ) :
    restrictedGowersNorm 1 Q f = ‖𝔼 x ∈ Q, f x‖ := by
  rw [restrictedGowersNorm, gowersNorm_one, gowersNorm_one,
    norm_expect_restrict_one, expect_restrictTo, Finset.expect_eq_sum_div_card]
  simp only [norm_div, Complex.norm_natCast]
  have hcard : (Q.card : ℝ) ≠ 0 := by exact_mod_cast hQ.card_pos.ne'
  have hH : (Fintype.card H : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

theorem gowersNorm_restrict_pow (j : ℕ) (Q : Finset H) (f : H → ℂ) :
    gowersNorm (j + 1) (restrictTo Q f) ^ (2 ^ (j + 1)) =
      (gowersMoment (j + 1) (restrictTo Q (fun _ ↦ 1))).re *
        restrictedGowersNorm (j + 1) Q f ^ (2 ^ (j + 1)) := by
  by_cases hQ : Q.Nonempty
  · rw [restrictedGowersNorm, div_pow, ← gowersNorm_pow]
    field_simp [(gowersNorm_restrict_one_pos j hQ).ne']
  · have he : Q = ∅ := Finset.not_nonempty_iff_eq_empty.mp hQ
    simp [he, restrictedGowersNorm, gowersNorm_zero]

omit [AddCommGroup H] [Fintype H] in
theorem restrictTo_add (Q : Finset H) (f g : H → ℂ) :
    restrictTo Q (fun x ↦ f x + g x) = fun x ↦ restrictTo Q f x + restrictTo Q g x := by
  funext x
  by_cases hx : x ∈ Q <;> simp [restrictTo, hx]

theorem restrictedGowersNorm_add (j : ℕ) (Q : Finset H) (f g : H → ℂ) :
    restrictedGowersNorm (j + 1) Q (fun x ↦ f x + g x) ≤
      restrictedGowersNorm (j + 1) Q f + restrictedGowersNorm (j + 1) Q g := by
  simp only [restrictedGowersNorm, restrictTo_add]
  rw [← add_div]
  exact div_le_div_of_nonneg_right (gowersNorm_add j _ _) (gowersNorm_nonneg j _)

theorem norm_mixedGowersMoment_restrict_le (j : ℕ) (Q : Finset H)
    (F : (Fin (j + 1) → Bool) → H → ℂ) :
    ‖mixedGowersMoment (j + 1) (fun ω ↦ restrictTo Q (F ω))‖ /
        (gowersMoment (j + 1) (restrictTo Q (fun _ ↦ 1))).re ≤
      ∏ ω, restrictedGowersNorm (j + 1) Q (F ω) := by
  simp only [restrictedGowersNorm, Finset.prod_div_distrib]
  rw [Finset.prod_const]
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  rw [gowersNorm_pow]
  exact div_le_div_of_nonneg_right (norm_mixedGowersMoment_le j _)
    (gowersMoment_re_nonneg j _)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G]

theorem multiplicativeDerivative_norm_le_one (f : G → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) (h x : G) : ‖multiplicativeDerivative f h x‖ ≤ 1 := by
  simpa only [multiplicativeDerivative, norm_mul, norm_star, one_mul] using
    mul_le_mul (hf x) (hf (x + h)) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)

variable [Fintype G]

theorem gowersNorm_le_one (s : ℕ) (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    gowersNorm (s + 1) f ≤ 1 := by
  apply gowersNorm_le_of_mean_norm_le_pow s f hf (by norm_num)
  simpa only [one_pow, Fintype.expect_const] using
    Finset.expect_le_expect (s := Finset.univ) (fun x _ => hf x)

def derivativeInverseBudget (s : ℕ) (p : ℝ) : ℝ := (2 ^ (s + 2) : ℕ) * p + 2

theorem derivativeInverseBudget_ge_two (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    2 ≤ derivativeInverseBudget s p := by
  unfold derivativeInverseBudget
  exact le_add_of_nonneg_left (mul_nonneg (Nat.cast_nonneg _) hp)

theorem exists_many_large_gowers_derivatives (s : ℕ) (f : G → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) {p : ℝ} (hp : 0 ≤ p)
    (hG : Real.exp (-p) ≤ gowersNorm (s + 2) f) :
    ∃ H : Finset G, H.Nonempty ∧
      Real.exp (-derivativeInverseBudget s p) * Fintype.card G ≤ (H.card : ℝ) ∧
      ∀ h ∈ H, Real.exp (-derivativeInverseBudget s p) ≤
        gowersNorm (s + 1) (multiplicativeDerivative f h) := by
  let a := Real.exp (-((2 ^ (s + 2) : ℕ) : ℝ) * p)
  have hmean : a ≤ 𝔼 h, gowersNorm (s + 1) (multiplicativeDerivative f h) ^
      (2 ^ (s + 1)) := by
    rw [← gowersNorm_derivative]
    calc
      a = Real.exp (-p) ^ (2 ^ (s + 2)) := by
        dsimp [a]
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      _ ≤ _ := pow_le_pow_left₀ (Real.exp_nonneg _) hG _
  have hunit (h : G) : gowersNorm (s + 1) (multiplicativeDerivative f h) ≤ 1 :=
    gowersNorm_le_one s _ (multiplicativeDerivative_norm_le_one f hf h)
  obtain ⟨H, hcard, hlarge⟩ := exists_dense_level_set
    (fun h => gowersNorm (s + 1) (multiplicativeDerivative f h) ^ (2 ^ (s + 1)))
    (Real.exp_nonneg _) (fun h => pow_le_one₀ (gowersNorm_nonneg s _) (hunit h)) hmean
  have hsmall : Real.exp (-derivativeInverseBudget s p) ≤ a / 2 := by
    calc
      _ ≤ Real.exp (-((2 ^ (s + 2) : ℕ) : ℝ) * p - 1) := by
        apply Real.exp_le_exp.mpr
        unfold derivativeInverseBudget
        linarith
      _ ≤ _ := exp_sub_one_le_half_exp _
  have hdense : Real.exp (-derivativeInverseBudget s p) * Fintype.card G ≤
      (H.card : ℝ) :=
    (mul_le_mul_of_nonneg_right hsmall (Nat.cast_nonneg _)).trans hcard
  have hnonempty : H.Nonempty := by
    apply Finset.card_pos.mp
    have hpos : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
    exact_mod_cast (mul_pos (Real.exp_pos _) hpos).trans_le hdense
  refine ⟨H, hnonempty, hdense, fun h hh => ?_⟩
  exact exp_neg_le_of_pow (gowersNorm_nonneg s _)
    (by linarith [derivativeInverseBudget_ge_two s hp])
    (pow_ne_zero _ (by norm_num)) (hsmall.trans (hlarge h hh))

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

def groupCubeSet (j : ℕ) (Q : Finset H) : Finset ((Fin j → H) × H) :=
  Finset.univ.filter (fun p ↦ ∀ ω : Fin j → Bool, p.2 + cubeShift p.1 ω ∈ Q)

def groupCubeCount (j : ℕ) (Q : Finset H) : ℕ := (groupCubeSet j Q).card

omit [Fintype H] in
theorem mixedCubeProduct_indicator (j : ℕ) (Q : Finset H) (hs : Fin j → H) (x : H) :
    mixedCubeProduct (fun _ ↦ restrictTo Q (fun _ ↦ 1)) hs x =
      if ∀ ω : Fin j → Bool, x + cubeShift hs ω ∈ Q then 1 else 0 := by
  have hv (ω : Fin j → Bool) :
      conjugationPower (booleanWeight ω) (restrictTo Q (fun _ ↦ 1) (x + cubeShift hs ω)) =
        if x + cubeShift hs ω ∈ Q then 1 else 0 := by
    by_cases hω : x + cubeShift hs ω ∈ Q <;> simp [restrictTo, hω]
  simp only [mixedCubeProduct, hv]
  by_cases hall : ∀ ω : Fin j → Bool, x + cubeShift hs ω ∈ Q
  · simp [hall]
  · rw [ite_eq_right hall]
    obtain ⟨ω, hω⟩ := not_forall.mp hall
    exact Finset.prod_eq_zero (Finset.mem_univ ω) (ite_eq_right hω)

theorem gowersMoment_indicator_eq_cubeCount (j : ℕ) (Q : Finset H) :
    gowersMoment j (restrictTo Q (fun _ ↦ 1)) =
      (groupCubeCount j Q : ℂ) / (Fintype.card H : ℂ) ^ (j + 1) := by
  rw [← mixedGowersMoment_const, mixedGowersMoment_eq_expect_cube]
  simp_rw [mixedCubeProduct_indicator]
  rw [← Finset.expect_product', Finset.univ_product_univ]
  rw [Fintype.expect_eq_sum_div_card]
  have hsum : (∑ p : (Fin j → H) × H,
      if ∀ ω : Fin j → Bool, p.2 + cubeShift p.1 ω ∈ Q then (1 : ℂ) else 0) =
        (groupCubeCount j Q : ℂ) := by
    simp [groupCubeCount, groupCubeSet]
  rw [hsum]
  simp [Fintype.card_prod, pow_succ]

theorem gowersMoment_indicator_re (j : ℕ) (Q : Finset H) :
    (gowersMoment j (restrictTo Q (fun _ ↦ 1))).re =
      (groupCubeCount j Q : ℝ) / (Fintype.card H : ℝ) ^ (j + 1) := by
  rw [gowersMoment_indicator_eq_cubeCount]
  simpa only [Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_natCast] using
    (Complex.ofReal_re ((groupCubeCount j Q : ℝ) / (Fintype.card H : ℝ) ^ (j + 1)))

theorem gowersNorm_restrict_cubeCount (j : ℕ) (Q : Finset H) (f : H → ℂ) :
    gowersNorm (j + 1) (restrictTo Q f) ^ (2 ^ (j + 1)) =
      ((groupCubeCount (j + 1) Q : ℝ) / (Fintype.card H : ℝ) ^ (j + 2)) *
        restrictedGowersNorm (j + 1) Q f ^ (2 ^ (j + 1)) := by
  rw [gowersNorm_restrict_pow, gowersMoment_indicator_re]

theorem card_le_groupCubeCount (j : ℕ) (Q : Finset H) : Q.card ≤ groupCubeCount j Q := by
  have hi : Function.Injective (fun x : H ↦ ((0 : Fin j → H), x)) := by
    intro x y h
    exact congrArg Prod.snd h
  have hsub : Q.image (fun x ↦ ((0 : Fin j → H), x)) ⊆ groupCubeSet j Q := by
    intro p hp
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro ω
    simpa [cubeShift] using hx
  calc
    Q.card = (Q.image (fun x ↦ ((0 : Fin j → H), x))).card :=
      (Finset.card_image_of_injective Q hi).symm
    _ ≤ groupCubeCount j Q := Finset.card_le_card hsub

theorem groupCubeCount_pos (j : ℕ) {Q : Finset H} (hQ : Q.Nonempty) :
    0 < groupCubeCount j Q := hQ.card_pos.trans_le (card_le_groupCubeCount j Q)

end Erdos3

end

section

namespace Erdos3

variable {G : Type*} [AddCommGroup G]

theorem cubeProduct_norm_le_one (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (hs : List G) (x : G) : ‖cubeProduct f hs x‖ ≤ 1 := by
  induction hs generalizing x with
  | nil => simpa only [cubeProduct_nil] using hf x
  | cons h hs ih =>
    rw [cubeProduct_cons, norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (ih x)).trans (ih (x + h))

theorem cubeProduct_mul (f g : G → ℂ) (hs : List G) (x : G) :
    cubeProduct (fun y => f y * g y) hs x = cubeProduct f hs x * cubeProduct g hs x := by
  induction hs generalizing x with
  | nil => simp only [cubeProduct_nil]
  | cons h hs ih =>
    simp only [cubeProduct_cons, ih, star_mul]
    ring

theorem cubeProduct_star (f : G → ℂ) (hs : List G) (x : G) :
    cubeProduct (fun y => star (f y)) hs x = star (cubeProduct f hs x) := by
  induction hs generalizing x with
  | nil => simp only [cubeProduct_nil]
  | cons h hs ih =>
    simp only [cubeProduct_cons, ih, star_mul, star_star]
    exact mul_comm _ _

theorem cubeProduct_tuple_cons {d : ℕ} (f : G → ℂ) (h : G)
    (u : Fin d → G) (x : G) :
    cubeProduct f (List.ofFn (Fin.cons h u)) x =
      cubeProduct (multiplicativeDerivative f h) (List.ofFn u) x := by
  rw [List.ofFn_cons, cubeProduct_cons_eq_derivative]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

noncomputable def additiveQuadrupleCorrelation (g : G → G → ℂ) (a h k : G) : ℝ :=
  ‖𝔼 x, star (g h x) * g (h - a) (x + a) * g k x * star (g (k - a) (x + a))‖

theorem derivative_correlations_force_additive_quadruples
    (f : G → ℂ) (g : G → G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    (𝔼 h, ‖𝔼 x, multiplicativeDerivative f h x * star (g h x)‖) ^ 4 ≤
      𝔼 a, 𝔼 h, 𝔼 k, additiveQuadrupleCorrelation g a h k := by
  let C (a : G) := 𝔼 h, ‖𝔼 x, multiplicativeDerivative f a x *
    (star (g h x) * g (h - a) (x + a))‖
  have hfirst : (𝔼 h, ‖𝔼 x, multiplicativeDerivative f h x * star (g h x)‖) ^ 2 ≤
      𝔼 a, C a := by
    have hcs := shifted_test_cauchy_schwarz f (fun x => star (f x))
      (fun h x => star (g h x)) (M := 1) (by simpa only [norm_star] using hf)
    have hreindex : (𝔼 h, 𝔼 k, ‖𝔼 x, f x * star (f (x + h - k)) *
        star (g h x) * g k (x + h - k)‖) = 𝔼 a, C a := by
      calc
        _ = 𝔼 h, 𝔼 a, ‖𝔼 x, multiplicativeDerivative f a x *
            (star (g h x) * g (h - a) (x + a))‖ := by
          apply Finset.expect_congr rfl
          intro h _
          apply Fintype.expect_equiv (Equiv.subLeft h)
          intro k
          simp only [Equiv.subLeft_apply, sub_sub_cancel, multiplicativeDerivative,
            ← add_sub_assoc, mul_assoc]
        _ = _ := Finset.expect_comm _ _ _
    rw [← hreindex]
    simpa only [one_pow, one_mul, star_star, multiplicativeDerivative, mul_assoc] using hcs
  have hsecond (a : G) : C a ^ 2 ≤
      𝔼 h, 𝔼 k, additiveQuadrupleCorrelation g a h k := by
    have hcs := finite_absolute_cauchy_schwarz (multiplicativeDerivative f a)
      (fun h x => star (g h x) * g (h - a) (x + a))
      (multiplicativeDerivative_norm_le_one f hf a)
    simpa only [one_pow, one_mul, C, additiveQuadrupleCorrelation, star_mul,
      star_star, mul_assoc, mul_comm, mul_left_comm] using hcs
  calc
    _ = ((𝔼 h, ‖𝔼 x, multiplicativeDerivative f h x * star (g h x)‖) ^ 2) ^ 2 := by ring
    _ ≤ (𝔼 a, C a) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) hfirst 2
    _ ≤ 𝔼 a, C a ^ 2 := expect_square_le C
    _ ≤ _ := Finset.expect_le_expect (fun a _ => hsecond a)

theorem additiveQuadrupleCorrelation_le_one (g : G → G → ℂ)
    (hg : ∀ h x, ‖g h x‖ ≤ 1) (a h k : G) : additiveQuadrupleCorrelation g a h k ≤ 1 := by
  apply (RCLike.norm_expect_le (K := ℂ)).trans
  apply Finset.expect_le Finset.univ_nonempty
  intro x _
  simp only [norm_mul, norm_star]
  refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (hg _ _)
  refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (hg _ _)
  exact (mul_le_of_le_one_left (norm_nonneg _) (hg _ _)).trans (hg _ _)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem derivative_correlation_energy_exchange (f : G → ℂ) (g : G → G → ℂ) :
    (𝔼 h, ‖finiteCorrelation Finset.univ (multiplicativeDerivative f h) (g h)‖ ^ 2) =
      𝔼 k, 𝔼 h, (finiteCorrelation Finset.univ
        (multiplicativeDerivative (multiplicativeDerivative f k) h)
        (multiplicativeDerivative (g h) k)).re := by
  calc
    _ = 𝔼 h, 𝔼 k, (finiteCorrelation Finset.univ
        (multiplicativeDerivative (multiplicativeDerivative f h) k)
        (multiplicativeDerivative (g h) k)).re := by
      apply Finset.expect_congr rfl
      intro h _
      exact correlation_sq_eq_expect_derivative (multiplicativeDerivative f h) (g h)
    _ = 𝔼 k, 𝔼 h, (finiteCorrelation Finset.univ
        (multiplicativeDerivative (multiplicativeDerivative f h) k)
        (multiplicativeDerivative (g h) k)).re := Finset.expect_comm _ _ _
    _ = _ := by
      apply Finset.expect_congr rfl
      intro k _
      apply Finset.expect_congr rfl
      intro h _
      rw [multiplicativeDerivative_comm]

theorem exists_many_exchanged_derivative_correlations
    (f : G → ℂ) (g : G → G → ℂ) (H : Finset G)
    (hf : ∀ x, ‖f x‖ ≤ 1) (hg : ∀ h x, ‖g h x‖ ≤ 1)
    (hzero : ∀ h, h ∉ H → ∀ x, g h x = 0)
    {α δ : ℝ} (hα : 0 < α) (hδ : 0 < δ)
    (hdense : α * Fintype.card G ≤ (H.card : ℝ))
    (hcorr : ∀ h ∈ H, δ ≤ ‖finiteCorrelation Finset.univ (multiplicativeDerivative f h) (g h)‖) :
    ∃ Q : Finset (G × G), Q.Nonempty ∧
      α * δ ^ 2 / 2 * (Fintype.card G : ℝ) ^ 2 ≤ (Q.card : ℝ) ∧
      ∀ t ∈ Q, t.2 ∈ H ∧ α * δ ^ 2 / 2 ≤
        (finiteCorrelation Finset.univ
          (multiplicativeDerivative (multiplicativeDerivative f t.1) t.2)
          (multiplicativeDerivative (g t.2) t.1)).re := by
  classical
  have hcard : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hmean : α * δ ^ 2 ≤
      𝔼 h, ‖finiteCorrelation Finset.univ (multiplicativeDerivative f h) (g h)‖ ^ 2 := by
    have hindicator : (𝔼 h : G, if h ∈ H then δ ^ 2 else 0) =
        (H.card : ℝ) * δ ^ 2 / Fintype.card G := by
      rw [Fintype.expect_eq_sum_div_card]
      simp
    calc
      _ ≤ (H.card : ℝ) * δ ^ 2 / Fintype.card G := by
        apply (le_div_iff₀ hcard).mpr
        nlinarith [mul_le_mul_of_nonneg_right hdense (sq_nonneg δ)]
      _ = _ := hindicator.symm
      _ ≤ _ := by
        apply Finset.expect_le_expect
        intro h _
        split_ifs with hh
        · exact pow_le_pow_left₀ hδ.le (hcorr h hh) 2
        · exact sq_nonneg _
  let value (t : G × G) := (finiteCorrelation Finset.univ
    (multiplicativeDerivative (multiplicativeDerivative f t.1) t.2)
    (multiplicativeDerivative (g t.2) t.1)).re
  have havg : α * δ ^ 2 ≤ 𝔼 t : G × G, value t := by
    rw [derivative_correlation_energy_exchange] at hmean
    simpa only [← Finset.univ_product_univ, Finset.expect_product, value] using hmean
  have hunit (t : G × G) : value t ≤ 1 :=
    (Complex.re_le_norm _).trans (norm_finiteCorrelation_le Finset.univ_nonempty _ _
      (fun x _ => multiplicativeDerivative_norm_le_one _
        (multiplicativeDerivative_norm_le_one f hf t.1) t.2 x)
      (fun x _ => multiplicativeDerivative_norm_le_one (g t.2) (hg t.2) t.1 x))
  obtain ⟨Q, hQsize, hQ⟩ := exists_dense_level_set value (by positivity : 0 ≤ α * δ ^ 2) hunit havg
  have hcards : (Fintype.card (G × G) : ℝ) = (Fintype.card G : ℝ) ^ 2 := by
    simp only [Fintype.card_prod, Nat.cast_mul, pow_two]
  rw [hcards] at hQsize
  have hQne : Q.Nonempty := by
    apply Finset.card_pos.mp
    exact_mod_cast lt_of_lt_of_le (by positivity : 0 < α * δ ^ 2 / 2 * (Fintype.card G : ℝ) ^ 2) hQsize
  refine ⟨Q, hQne, hQsize, ?_⟩
  intro t ht
  have hpositive : 0 < value t := lt_of_lt_of_le (by positivity) (hQ t ht)
  have hmem : t.2 ∈ H := by
    by_contra hn
    simp [value, finiteCorrelation, multiplicativeDerivative, hzero t.2 hn] at hpositive
  exact ⟨hmem, hQ t ht⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem conjugationPower_norm (n : ℕ) (z : ℂ) : ‖conjugationPower n z‖ = ‖z‖ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ‖star (conjugationPower n z)‖ = ‖z‖
    rw [norm_star, ih]

theorem cubeProduct_eq_mixedCubeProduct {H : Type*} [AddCommGroup H]
    (f : H → ℂ) {d : ℕ} (k : Fin d → H) (x : H) :
    cubeProduct f (List.ofFn k) x = mixedCubeProduct (fun _ => f) k x := by
  induction d generalizing x with
  | zero => simp only [List.ofFn_zero, cubeProduct_nil, mixedCubeProduct_zero]
  | succ d ih =>
    rw [← Fin.cons_self_tail k, List.ofFn_cons, cubeProduct_cons, mixedCubeProduct_cons]
    rw [ih, ih]

theorem cubeProduct_eq_boolean_product {H : Type*} [AddCommGroup H]
    (f : H → ℂ) {d : ℕ} (k : Fin d → H) (x : H) :
    cubeProduct f (List.ofFn k) x =
      ∏ ω : Fin d → Bool, conjugationPower (booleanWeight ω) (f (x + cubeShift k ω)) :=
  cubeProduct_eq_mixedCubeProduct f k x

end Erdos3

end

end OAI
