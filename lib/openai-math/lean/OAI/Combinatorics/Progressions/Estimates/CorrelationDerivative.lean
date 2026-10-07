import Mathlib.Algebra.BigOperators.Fin
import OAI.Combinatorics.Progressions.Estimates.WeightedSummandCorrelation
import OAI.Combinatorics.Progressions.Probability.FiniteProbabilityLipschitz
import OAI.Combinatorics.Progressions.Sampling.ModelScoreComparison

namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H]

def multiplicativeDerivative (f : H → ℂ) (h : H) : H → ℂ :=
  fun x ↦ f x * star (f (x + h))

noncomputable def gowersMoment : ℕ → (H → ℂ) → ℂ
  | 0, f => 𝔼 x, f x
  | j + 1, f => 𝔼 h, gowersMoment j (multiplicativeDerivative f h)

omit [AddCommGroup H] in
theorem expect_star (f : H → ℂ) : (𝔼 x, star (f x)) = star (𝔼 x, f x) := by
  simp [Fintype.expect_eq_sum_div_card]

omit [AddCommGroup H] in
theorem expect_re (f : H → ℂ) : (𝔼 x, f x).re = 𝔼 x, (f x).re := by
  simp [Fintype.expect_eq_sum_div_card]

omit [AddCommGroup H] in
theorem expect_im (f : H → ℂ) : (𝔼 x, f x).im = 𝔼 x, (f x).im := by
  simp [Fintype.expect_eq_sum_div_card]

theorem expect_translate (f : H → ℂ) (x : H) : (𝔼 h, f (x + h)) = 𝔼 h, f h := by
  exact Fintype.expect_equiv (Equiv.addLeft x) _ f (fun _ ↦ rfl)

omit [Fintype H] in
theorem multiplicativeDerivative_comm (f : H → ℂ) (h k : H) :
    multiplicativeDerivative (multiplicativeDerivative f h) k =
      multiplicativeDerivative (multiplicativeDerivative f k) h := by
  funext x
  simp only [multiplicativeDerivative, star_mul, star_star]
  rw [show x + k + h = x + h + k by abel]
  ring

theorem gowersMoment_one (f : H → ℂ) :
    gowersMoment 1 f = (𝔼 x, f x) * star (𝔼 x, f x) := by
  change (𝔼 h, 𝔼 x, f x * star (f (x + h))) = _
  rw [Finset.expect_comm]
  calc
    (𝔼 x, 𝔼 h, f x * star (f (x + h))) =
        𝔼 x, f x * star (𝔼 h, f h) := by
      apply Finset.expect_congr rfl
      intro x hx
      rw [← Finset.mul_expect, expect_translate (fun h ↦ star (f h)), expect_star]
    _ = _ := (Finset.expect_mul _ _ _).symm

theorem gowersMoment_re_nonneg (j : ℕ) (f : H → ℂ) :
    0 ≤ (gowersMoment (j + 1) f).re := by
  induction j generalizing f with
  | zero =>
    rw [gowersMoment_one]
    change 0 ≤ ((𝔼 x, f x) * starRingEnd ℂ (𝔼 x, f x)).re
    rw [Complex.mul_conj, Complex.ofReal_re]
    exact Complex.normSq_nonneg _
  | succ j ih =>
    rw [gowersMoment, expect_re]
    exact Finset.expect_nonneg (fun h _ ↦ ih (multiplicativeDerivative f h))

theorem gowersMoment_im_zero (j : ℕ) (f : H → ℂ) :
    (gowersMoment (j + 1) f).im = 0 := by
  induction j generalizing f with
  | zero =>
    rw [gowersMoment_one]
    change ((𝔼 x, f x) * starRingEnd ℂ (𝔼 x, f x)).im = 0
    rw [Complex.mul_conj, Complex.ofReal_im]
  | succ j ih =>
    rw [gowersMoment, expect_im]
    exact Finset.expect_eq_zero (fun h _ ↦ ih (multiplicativeDerivative f h))

theorem gowersMoment_const_one (j : ℕ) : gowersMoment j (fun _ : H ↦ 1) = 1 := by
  induction j with
  | zero => simp [gowersMoment]
  | succ j ih =>
    change (𝔼 h : H, gowersMoment j (multiplicativeDerivative (fun _ : H ↦ 1) h)) = 1
    have hder (h : H) : multiplicativeDerivative (fun _ : H ↦ 1) h = (fun _ : H ↦ 1) := by
      funext x
      simp [multiplicativeDerivative]
    simp_rw [hder, ih]
    exact Fintype.expect_one (ι := H)

noncomputable def gowersNorm (j : ℕ) (f : H → ℂ) : ℝ :=
  (gowersMoment j f).re ^ (((2 ^ j : ℕ) : ℝ)⁻¹)

theorem gowersNorm_nonneg (j : ℕ) (f : H → ℂ) : 0 ≤ gowersNorm (j + 1) f :=
  Real.rpow_nonneg (gowersMoment_re_nonneg j f) _

theorem gowersNorm_pow (j : ℕ) (f : H → ℂ) :
    gowersNorm (j + 1) f ^ (2 ^ (j + 1)) = (gowersMoment (j + 1) f).re := by
  exact Real.rpow_inv_natCast_pow (n := 2 ^ (j + 1)) (gowersMoment_re_nonneg j f)
    (pow_ne_zero _ (by norm_num))

theorem gowersNorm_one (f : H → ℂ) : gowersNorm 1 f = ‖𝔼 x, f x‖ := by
  have hmoment : (gowersMoment 1 f).re = ‖𝔼 x, f x‖ ^ 2 := by
    rw [gowersMoment_one]
    change ((𝔼 x, f x) * starRingEnd ℂ (𝔼 x, f x)).re = _
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  unfold gowersNorm
  rw [hmoment]
  norm_num only [pow_one, Nat.cast_ofNat]
  simpa using Real.pow_rpow_inv_natCast (norm_nonneg (𝔼 x : H, f x))
    (by norm_num : (2 : ℕ) ≠ 0)

theorem gowersNorm_const_one (j : ℕ) : gowersNorm j (fun _ : H ↦ 1) = 1 := by
  simp [gowersNorm, gowersMoment_const_one]

theorem gowersNorm_derivative (j : ℕ) (f : H → ℂ) :
    gowersNorm (j + 2) f ^ (2 ^ (j + 2)) =
      𝔼 h, gowersNorm (j + 1) (multiplicativeDerivative f h) ^ (2 ^ (j + 1)) := by
  simp only [gowersNorm_pow]
  exact expect_re _

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

def conjugationPower : ℕ → (ℂ →+* ℂ)
  | 0 => RingHom.id ℂ
  | n + 1 => (starRingEnd ℂ).comp (conjugationPower n)

theorem conjugationPower_star (n : ℕ) (z : ℂ) :
    conjugationPower n (star z) = star (conjugationPower n z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change star (conjugationPower n (star z)) = star (star (conjugationPower n z))
    exact congrArg star ih

variable {H : Type*} [AddCommGroup H]

def cubeProduct (f : H → ℂ) (hs : List H) (x : H) : ℂ :=
  (hs.sublists'.map fun ks ↦ conjugationPower ks.length (f (x + ks.sum))).prod

@[simp] theorem cubeProduct_nil (f : H → ℂ) (x : H) : cubeProduct f [] x = f x := by
  simp [cubeProduct, conjugationPower]

theorem cubeProduct_cons (f : H → ℂ) (h : H) (hs : List H) (x : H) :
    cubeProduct f (h :: hs) x = cubeProduct f hs x * star (cubeProduct f hs (x + h)) := by
  simp only [cubeProduct, List.sublists'_cons, List.map_append, List.prod_append,
    List.map_map, Function.comp_def, List.length_cons, List.sum_cons,
    conjugationPower, RingHom.comp_apply]
  congr 1
  change _ = (starRingEnd ℂ) _
  rw [map_list_prod, List.map_map]
  simp only [Function.comp_def, add_assoc]

theorem cubeProduct_derivative (f : H → ℂ) (h : H) (hs : List H) (x : H) :
    cubeProduct (multiplicativeDerivative f h) hs x =
      cubeProduct f hs x * star (cubeProduct f hs (x + h)) := by
  induction hs generalizing x with
  | nil => simp [multiplicativeDerivative]
  | cons k hs ih =>
    simp only [cubeProduct_cons, ih, star_mul, star_star]
    rw [show x + k + h = x + h + k by abel]
    ring

theorem cubeProduct_cons_eq_derivative (f : H → ℂ) (h : H) (hs : List H) (x : H) :
    cubeProduct f (h :: hs) x = cubeProduct (multiplicativeDerivative f h) hs x := by
  rw [cubeProduct_cons, cubeProduct_derivative]

variable [Fintype H]

noncomputable def cubeAverage {M : Type*} [AddCommMonoid M] [Module ℚ≥0 M] :
    ℕ → (List H → M) → M
  | 0, F => F []
  | j + 1, F => 𝔼 h, cubeAverage j (fun hs ↦ F (h :: hs))

omit [AddCommGroup H] in

theorem cubeAverage_eq_expect_tuple {M : Type*} [AddCommMonoid M] [Module ℚ≥0 M]
    (j : ℕ) (F : List H → M) :
    cubeAverage j F = 𝔼 h : Fin j → H, F (List.ofFn h) := by
  induction j generalizing F with
  | zero => simp [cubeAverage]
  | succ j ih =>
    rw [cubeAverage, expect_fin_cons]
    apply Finset.expect_congr rfl
    intro h hh
    rw [ih]
    apply Finset.expect_congr rfl
    intro hs hhs
    simp

omit [AddCommGroup H] in
theorem cubeAverage_re (j : ℕ) (F : List H → ℂ) :
    (cubeAverage j F).re = cubeAverage j (fun hs ↦ (F hs).re) := by
  simp only [cubeAverage_eq_expect_tuple, expect_re]

omit [AddCommGroup H] in
theorem cubeAverage_comm_expect {Ω : Type*} [Fintype Ω]
    {M : Type*} [AddCommMonoid M] [Module ℚ≥0 M] (j : ℕ) (F : List H → Ω → M) :
    cubeAverage j (fun hs ↦ 𝔼 x, F hs x) = 𝔼 x, cubeAverage j (fun hs ↦ F hs x) := by
  simp only [cubeAverage_eq_expect_tuple]
  exact Finset.expect_comm _ _ _

omit [AddCommGroup H] in
theorem cubeAverage_norm_inner_sq_le (j : ℕ) (F G : List H → ℂ) :
    ‖cubeAverage j (fun hs ↦ F hs * star (G hs))‖ ^ 2 ≤
      cubeAverage j (fun hs ↦ ‖F hs‖ ^ 2) * cubeAverage j (fun hs ↦ ‖G hs‖ ^ 2) := by
  simp only [cubeAverage_eq_expect_tuple]
  exact norm_expect_mul_star_sq_le _ _

theorem gowersMoment_eq_cubeAverage (j : ℕ) (f : H → ℂ) :
    gowersMoment j f = cubeAverage j (fun hs ↦ 𝔼 x, cubeProduct f hs x) := by
  induction j generalizing f with
  | zero => simp [gowersMoment, cubeAverage]
  | succ j ih =>
    simp only [gowersMoment, cubeAverage, ih, cubeProduct_cons_eq_derivative]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem expect_pair_sub_real (F : G → ℝ) :
    (𝔼 h, 𝔼 k, F (h - k)) = 𝔼 d, F d := by
  rw [Finset.expect_comm]
  have hinner (k : G) : (𝔼 h, F (h - k)) = 𝔼 d, F d := by
    apply Fintype.expect_equiv (Equiv.addRight (-k))
    intro h
    simp only [Equiv.coe_addRight, sub_eq_add_neg]
  simp_rw [hinner]
  exact Fintype.expect_const _

theorem gowersNorm_pow_lower_of_pair_detector (j : ℕ) (v : G → ℂ)
    (C : G → G → ℝ) {alpha delta gamma : ℝ}
    (hdelta : 0 ≤ delta) (hgamma : 0 ≤ gamma)
    (hC : ∀ h k, C h k ≤ 1) (hmean : alpha ≤ 𝔼 h, 𝔼 k, C h k)
    (hdetect : ∀ h k, delta ≤ C h k →
      gamma ≤ gowersNorm (j + 1) (multiplicativeDerivative v (h - k))) :
    gamma ^ (2 ^ (j + 1)) * (alpha - delta) ≤
      gowersNorm (j + 2) v ^ (2 ^ (j + 2)) := by
  have hpoint (h k : G) :
      gamma ^ (2 ^ (j + 1)) * (C h k - delta) ≤
        gowersNorm (j + 1) (multiplicativeDerivative v (h - k)) ^ (2 ^ (j + 1)) := by
    by_cases hlarge : delta ≤ C h k
    · have hpow := pow_le_pow_left₀ hgamma (hdetect h k hlarge) (2 ^ (j + 1))
      have hsmall : C h k - delta ≤ 1 := by linarith [hC h k]
      exact (mul_le_of_le_one_right (pow_nonneg hgamma _) hsmall).trans hpow
    · have hleft : gamma ^ (2 ^ (j + 1)) * (C h k - delta) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hgamma _) (by linarith)
      exact hleft.trans (pow_nonneg (gowersNorm_nonneg j _) _)
  have h := Finset.expect_le_expect (fun h (_ : h ∈ (Finset.univ : Finset G)) =>
    Finset.expect_le_expect (fun k (_ : k ∈ (Finset.univ : Finset G)) => hpoint h k))
  simp_rw [← Finset.mul_expect, Finset.expect_sub_distrib,
    Finset.expect_const Finset.univ_nonempty] at h
  rw [expect_pair_sub_real (fun a =>
    gowersNorm (j + 1) (multiplicativeDerivative v a) ^ (2 ^ (j + 1))),
    ← gowersNorm_derivative] at h
  exact (mul_le_mul_of_nonneg_left (sub_le_sub_right hmean delta) (pow_nonneg hgamma _)).trans h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_quartic_diagonal_weights {N : ℕ} [NeZero N]
    (f : ZMod N → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (A : Fin 4 → (Fin 4 → ℤ) → ℂ) (hA : ∀ i x, ‖A i x‖ ≤ 1)
    (hAind : ∀ i x y, (∀ k, k ≠ i → x k = y k) → A i x = A i y) :
    ∃ B : Fin 4 → (Fin 4 → ℤ) → ℂ,
      (∀ i x, ‖B i x‖ ≤ 1) ∧
      (∀ i x y, (∀ k, k ≠ i → x k = y k) → B i x = B i y) ∧
      ∀ (x : Fin 4 → ℤ) (z : ℂ),
        (multiplicativeDerivative
          (multiplicativeDerivative (multiplicativeDerivative f (x 2 : ZMod N)) (x 3 : ZMod N))
          (x 0 : ZMod N) (x 1 : ZMod N) * z) * ∏ i, A i x =
        star (f ((x 1 + x 0 + x 2 + x 3 : ℤ) : ZMod N)) * z * ∏ i, B i x := by
  let c (x : Fin 4 → ℤ) : Fin 4 → ℂ :=
    ![f (x 1 : ZMod N) * star (f ((x 1 + x 2 : ℤ) : ZMod N)) *
        star (f ((x 1 + x 3 : ℤ) : ZMod N)) * f ((x 1 + x 2 + x 3 : ℤ) : ZMod N),
      1,
      star (f ((x 1 + x 0 : ℤ) : ZMod N)) * f ((x 1 + x 0 + x 3 : ℤ) : ZMod N),
      f ((x 1 + x 0 + x 2 : ℤ) : ZMod N)]
  let B (i : Fin 4) (x : Fin 4 → ℤ) := A i x * c x i
  have hc : ∀ i x, ‖c x i‖ ≤ 1 := by
    intro i x
    fin_cases i
    · change ‖f _ * star (f _) * star (f _) * f _‖ ≤ 1
      rw [norm_mul, norm_mul, norm_mul, norm_star, norm_star]
      refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (hf _)
      refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (hf _)
      exact (mul_le_of_le_one_left (norm_nonneg _) (hf _)).trans (hf _)
    · change ‖(1 : ℂ)‖ ≤ 1
      simp only [norm_one, le_refl]
    · change ‖star (f _) * f _‖ ≤ 1
      rw [norm_mul, norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hf _)).trans (hf _)
    · exact hf _
  have hind : ∀ i x y, (∀ k, k ≠ i → x k = y k) → c x i = c y i := by
    intro i x y hxy
    fin_cases i
    · change f (x 1 : ZMod N) * star (f ((x 1 + x 2 : ℤ) : ZMod N)) *
          star (f ((x 1 + x 3 : ℤ) : ZMod N)) * f ((x 1 + x 2 + x 3 : ℤ) : ZMod N) =
        f (y 1 : ZMod N) * star (f ((y 1 + y 2 : ℤ) : ZMod N)) *
          star (f ((y 1 + y 3 : ℤ) : ZMod N)) * f ((y 1 + y 2 + y 3 : ℤ) : ZMod N)
      rw [hxy 1 (by decide), hxy 2 (by decide), hxy 3 (by decide)]
    · rfl
    · change star (f ((x 1 + x 0 : ℤ) : ZMod N)) * f ((x 1 + x 0 + x 3 : ℤ) : ZMod N) =
        star (f ((y 1 + y 0 : ℤ) : ZMod N)) * f ((y 1 + y 0 + y 3 : ℤ) : ZMod N)
      rw [hxy 0 (by decide), hxy 1 (by decide), hxy 3 (by decide)]
    · change f ((x 1 + x 0 + x 2 : ℤ) : ZMod N) = f ((y 1 + y 0 + y 2 : ℤ) : ZMod N)
      rw [hxy 0 (by decide), hxy 1 (by decide), hxy 2 (by decide)]
  refine ⟨B, ?_, ?_, ?_⟩
  · intro i x
    change ‖A i x * c x i‖ ≤ 1
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hA i x)).trans (hc i x)
  · intro i x y hxy
    change A i x * c x i = A i y * c y i
    rw [hAind i x y hxy, hind i x y hxy]
  · intro x z
    simp only [B, c, Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, multiplicativeDerivative,
      star_mul, star_star, Int.cast_add]
    simp only [add_assoc, add_comm, add_left_comm]
    ring

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {Ω H : Type*} [Fintype Ω] (p : FiniteProbabilityWeights Ω)

noncomputable def complexMean (v : Ω → ℂ) : ℂ := ∑ x, (p.weight x : ℂ) * v x

theorem correlation_eq_complexMean (v w : Ω → ℂ) :
    p.correlation v w = p.complexMean (fun x => v x * star (w x)) := rfl

theorem complexMean_eq_correlation_one (v : Ω → ℂ) :
    p.complexMean v = p.correlation v (fun _ => 1) := by
  simp only [correlation, complexMean, star_one, mul_one]

theorem complexMean_mul_left (a : ℂ) (v : Ω → ℂ) :
    p.complexMean (fun x => a * v x) = a * p.complexMean v := by
  unfold complexMean
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem complexMean_re (v : Ω → ℂ) :
    (p.complexMean v).re = p.mean (fun x => (v x).re) := by
  simp [complexMean, mean, Complex.mul_re]

theorem norm_complexMean_sq_le (v : Ω → ℂ) :
    ‖p.complexMean v‖ ^ 2 ≤ p.mean (fun x => ‖v x‖ ^ 2) := by
  rw [p.complexMean_eq_correlation_one]
  have h := p.norm_correlation_sq_le v (fun _ => 1)
  simpa only [norm_one, one_pow, p.mean_const, mul_one] using h

theorem mean_norm_sq_le_one (v : Ω → ℂ) (hv : ∀ x, ‖v x‖ ≤ 1) :
    p.mean (fun x => ‖v x‖ ^ 2) ≤ 1 := by
  apply (p.mean_mono (fun x => ?_)).trans_eq (p.mean_const 1)
  nlinarith [hv x, norm_nonneg (v x)]

theorem norm_correlation_le_one (v w : Ω → ℂ)
    (hv : ∀ x, ‖v x‖ ≤ 1) (hw : ∀ x, ‖w x‖ ≤ 1) : ‖p.correlation v w‖ ≤ 1 := by
  have hcs := p.norm_correlation_sq_le v w
  have hprod := (mul_le_of_le_one_left (p.mean_nonneg (fun x => sq_nonneg ‖w x‖))
    (p.mean_norm_sq_le_one v hv)).trans (p.mean_norm_sq_le_one w hw)
  nlinarith [norm_nonneg (p.correlation v w)]

theorem correlation_mul_phases (v w : Ω → ℂ) (a b : ℂ) :
    p.correlation (fun x => a * v x) (fun x => b * w x) =
      (a * star b) * p.correlation v w := by
  unfold correlation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [star_mul]
  ring

theorem norm_correlation_mul_phases (v w : Ω → ℂ) {a b : ℂ}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    ‖p.correlation (fun x => a * v x) (fun x => b * w x)‖ = ‖p.correlation v w‖ := by
  rw [p.correlation_mul_phases, norm_mul, norm_mul, norm_star, ha, hb, one_mul, one_mul]

variable [Fintype H]

theorem complexMean_average (v : H → Ω → ℂ) :
    p.complexMean (fun x => 𝔼 h, v h x) = 𝔼 h, p.complexMean (v h) := by
  unfold complexMean
  simp_rw [Finset.mul_expect]
  exact (Finset.expect_sum_comm _ _ _).symm

theorem correlation_average_left (v : H → Ω → ℂ) (w : Ω → ℂ) :
    p.correlation (fun x => 𝔼 h, v h x) w = 𝔼 h, p.correlation (v h) w := by
  unfold correlation
  simp_rw [Finset.expect_mul, Finset.mul_expect]
  exact (Finset.expect_sum_comm _ _ _).symm

theorem correlation_average_right (v : Ω → ℂ) (w : H → Ω → ℂ) :
    p.correlation v (fun x => 𝔼 h, w h x) = 𝔼 h, p.correlation v (w h) := by
  unfold correlation
  simp_rw [← expect_star, Finset.mul_expect]
  exact (Finset.expect_sum_comm _ _ _).symm

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def finiteWeightedTest {Ω T : Type*} [Fintype T]
    (ψ : T → Ω) (w : T → ℂ) : (Ω → ℂ) →ₗ[ℂ] ℂ where
  toFun v := 𝔼 t, w t * v (ψ t)
  map_add' v z := by simp only [Pi.add_apply, mul_add, Finset.expect_add_distrib]
  map_smul' c v := by
    change (𝔼 t, w t * (c * v (ψ t))) = c * (𝔼 t, w t * v (ψ t))
    rw [Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro t _
    ring

theorem finiteWeightedTest_real {Ω T : Type*} [Fintype T]
    (ψ : T → Ω) (w : T → ℝ) (v : Ω → ℝ) :
    (finiteWeightedTest ψ (fun t => (w t : ℂ)) (fun x => (v x : ℂ))).re =
      𝔼 t, w t * v (ψ t) := by
  change (𝔼 t, (w t : ℂ) * (v (ψ t) : ℂ)).re = _
  rw [expect_re]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

theorem finite_weighted_model_score_transfer {Ω T U I : Type*}
    [Fintype T] [Fintype U] [Fintype I]
    (ψ : T → Ω) (φ : U → Ω) (w : T → ℝ) (z : U → ℝ)
    (v : Ω → ℝ) (e : Ω → ℂ) (J : I → Ω → ℂ) (c : I → ℂ)
    (hmodel : (fun x => (v x : ℂ)) = (∑ i, c i • J i) + e) {M η α β S : ℝ}
    (hη : 0 ≤ η) (hc : (∑ i, ‖c i‖) ≤ M)
    (hatom : ∀ i, ‖(𝔼 t, (w t : ℂ) * J i (ψ t)) - (𝔼 u, (z u : ℂ) * J i (φ u))‖ ≤ η)
    (heA : ‖𝔼 t, (w t : ℂ) * e (ψ t)‖ ≤ α)
    (heB : ‖𝔼 u, (z u : ℂ) * e (φ u)‖ ≤ β)
    (hscore : S ≤ 𝔼 u, z u * v (φ u)) :
    S - (M * η + α + β) ≤ 𝔼 t, w t * v (ψ t) := by
  have h := finite_model_score_transfer
    (finiteWeightedTest ψ (fun t => (w t : ℂ))) (finiteWeightedTest φ (fun u => (z u : ℂ)))
    (fun x => (v x : ℂ)) e J c hmodel hη hc hatom heA heB
    (by simpa only [finiteWeightedTest_real] using hscore)
  simpa only [finiteWeightedTest_real] using h

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H]

def crossDerivative (f g : H → ℂ) (h : H) : H → ℂ :=
  fun x ↦ f x * star (g (x + h))

omit [Fintype H] in
@[simp] theorem crossDerivative_self (f : H → ℂ) (h : H) :
    crossDerivative f f h = multiplicativeDerivative f h := rfl

omit [Fintype H] in
theorem cubeProduct_crossDerivative (f g : H → ℂ) (h : H) (hs : List H) (x : H) :
    cubeProduct (crossDerivative f g h) hs x =
      cubeProduct f hs x * star (cubeProduct g hs (x + h)) := by
  induction hs generalizing x with
  | nil => simp [crossDerivative]
  | cons k hs ih =>
    simp only [cubeProduct_cons, ih, star_mul, star_star]
    rw [show x + k + h = x + h + k by abel]
    ring

theorem expect_crossDerivative (f g : H → ℂ) :
    (𝔼 h, 𝔼 x, crossDerivative f g h x) = (𝔼 x, f x) * star (𝔼 x, g x) := by
  change (𝔼 h, 𝔼 x, f x * star (g (x + h))) = _
  rw [Finset.expect_comm]
  calc
    (𝔼 x, 𝔼 h, f x * star (g (x + h))) = 𝔼 x, f x * star (𝔼 y, g y) := by
      apply Finset.expect_congr rfl
      intro x hx
      rw [← Finset.mul_expect, expect_translate (fun y ↦ star (g y)), expect_star]
    _ = _ := (Finset.expect_mul _ _ _).symm

theorem expect_gowersMoment_crossDerivative (j : ℕ) (f g : H → ℂ) :
    (𝔼 h, gowersMoment j (crossDerivative f g h)) =
      cubeAverage j (fun hs ↦ (𝔼 x, cubeProduct f hs x) * star (𝔼 x, cubeProduct g hs x)) := by
  simp only [gowersMoment_eq_cubeAverage]
  rw [← cubeAverage_comm_expect]
  simp_rw [cubeProduct_crossDerivative]
  have hpoint : ∀ hs : List H,
      (𝔼 h, 𝔼 x, cubeProduct f hs x * star (cubeProduct g hs (x + h))) =
        (𝔼 x, cubeProduct f hs x) * star (𝔼 x, cubeProduct g hs x) := by
    intro hs
    exact expect_crossDerivative (cubeProduct f hs) (cubeProduct g hs)
  simp_rw [hpoint]

theorem mul_star_re_eq_norm_sq (z : ℂ) : (z * star z).re = ‖z‖ ^ 2 := by
  change (z * (starRingEnd ℂ) z).re = ‖z‖ ^ 2
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

theorem gowersMoment_eq_average_square (j : ℕ) (f : H → ℂ) :
    (gowersMoment (j + 1) f).re =
      cubeAverage j (fun hs ↦ ‖𝔼 x, cubeProduct f hs x‖ ^ 2) := by
  have h := congrArg Complex.re (expect_gowersMoment_crossDerivative j f f)
  change (𝔼 h, gowersMoment j (multiplicativeDerivative f h)).re = _
  simpa only [crossDerivative_self, cubeAverage_re,
    mul_star_re_eq_norm_sq] using h

theorem norm_expect_gowersMoment_crossDerivative_sq_le (j : ℕ) (f g : H → ℂ) :
    ‖𝔼 h, gowersMoment j (crossDerivative f g h)‖ ^ 2 ≤
      (gowersMoment (j + 1) f).re * (gowersMoment (j + 1) g).re := by
  rw [expect_gowersMoment_crossDerivative,
    gowersMoment_eq_average_square, gowersMoment_eq_average_square]
  exact cubeAverage_norm_inner_sq_le j _ _

theorem expect_cross_gowersNorm_pow_le (j : ℕ) (f g : H → ℂ) :
    (𝔼 h, gowersNorm (j + 1) (crossDerivative f g h) ^ (2 ^ (j + 1))) ≤
      (gowersNorm (j + 2) f * gowersNorm (j + 2) g) ^ (2 ^ (j + 1)) := by
  let A := 𝔼 h, gowersNorm (j + 1) (crossDerivative f g h) ^ (2 ^ (j + 1))
  let B := (gowersNorm (j + 2) f * gowersNorm (j + 2) g) ^ (2 ^ (j + 1))
  have hA : 0 ≤ A := Finset.expect_nonneg (fun h _ ↦
    pow_nonneg (gowersNorm_nonneg j _) _)
  have hB : 0 ≤ B := pow_nonneg
    (mul_nonneg (gowersNorm_nonneg (j + 1) f) (gowersNorm_nonneg (j + 1) g)) _
  have hnorm : A ≤ ‖𝔼 h, gowersMoment (j + 1) (crossDerivative f g h)‖ := by
    dsimp [A]
    simp only [gowersNorm_pow, ← expect_re]
    exact Complex.re_le_norm _
  have hpower : (gowersMoment (j + 2) f).re * (gowersMoment (j + 2) g).re = B ^ 2 := by
    dsimp [B]
    rw [← gowersNorm_pow, ← gowersNorm_pow, ← mul_pow, ← pow_mul]
    congr 1
  have hsq : A ^ 2 ≤ B ^ 2 := (pow_le_pow_left₀ hA hnorm 2).trans
    ((norm_expect_gowersMoment_crossDerivative_sq_le (j + 1) f g).trans_eq hpower)
  change A ≤ B
  nlinarith

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {J : Type*} [Fintype J] [DecidableEq J] {Ω : J → Type*} [∀ j, Fintype (Ω j)]

noncomputable def pi (p : ∀ j, FiniteProbabilityWeights (Ω j)) :
    FiniteProbabilityWeights (∀ j, Ω j) := by
  classical
  exact {
    weight := fun x => ∏ j, (p j).weight (x j)
    nonneg := fun x => Finset.prod_nonneg (fun j _ => (p j).nonneg (x j))
    total := by
      calc
        _ = ∏ j, ∑ x, (p j).weight x := (Fintype.prod_sum _).symm
        _ = ∏ _j : J, (1 : ℝ) := Finset.prod_congr rfl (fun j _ => (p j).total)
        _ = 1 := by simp }

theorem complexMean_pi_product (p : ∀ j, FiniteProbabilityWeights (Ω j))
    (v : ∀ j, Ω j → ℂ) :
    (pi p).complexMean (fun x => ∏ j, v j (x j)) = ∏ j, (p j).complexMean (v j) := by
  classical
  change (∑ x : ∀ j, Ω j, ((∏ j, (p j).weight (x j) : ℝ) : ℂ) * (∏ j, v j (x j))) =
    ∏ j, ∑ x, ((p j).weight x : ℂ) * v j x
  simp_rw [Complex.ofReal_prod, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun j (x : Ω j) => ((p j).weight x : ℂ) * v j x)).symm

theorem correlation_pi_product (p : ∀ j, FiniteProbabilityWeights (Ω j))
    (v w : ∀ j, Ω j → ℂ) :
    (pi p).correlation (fun x => ∏ j, v j (x j)) (fun x => ∏ j, w j (x j)) =
      ∏ j, (p j).correlation (v j) (w j) := by
  classical
  change (pi p).complexMean (fun x => (∏ j, v j (x j)) * star (∏ j, w j (x j))) =
    ∏ j, (p j).complexMean (fun x => v j x * star (w j x))
  simp_rw [star_prod, ← Finset.prod_mul_distrib]
  exact complexMean_pi_product p (fun j x => v j x * star (w j x))

end Erdos3.FiniteProbabilityWeights

end

section

open scoped BigOperators

namespace Erdos3

theorem density_large_values_of_expect {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (a : Ω → ℝ) {r B : ℝ} (hr : 0 ≤ r) (hB : 0 < B)
    (ha : ∀ x, a x ≤ B) (hmean : r ≤ 𝔼 x, a x) :
    r / (2 * B) ≤ 𝔼 x, if r / 2 ≤ a x then (1 : ℝ) else 0 := by
  classical
  have hpoint (x : Ω) : a x ≤ r / 2 + B * (if r / 2 ≤ a x then (1 : ℝ) else 0) := by
    split_ifs with hx
    · simp only [mul_one]
      linarith [ha x]
    · simp only [mul_zero, add_zero]
      exact (lt_of_not_ge hx).le
  have hsum := Finset.expect_le_expect (fun x (_ : x ∈ (Finset.univ : Finset Ω)) => hpoint x)
  rw [Finset.expect_add_distrib, Fintype.expect_const, ← Finset.mul_expect] at hsum
  apply (div_le_iff₀ (by positivity : 0 < 2 * B)).mpr
  nlinarith

variable {H : Type*} [AddCommGroup H] [Fintype H]

theorem correlation_sq_eq_expect_derivative (f u : H → ℂ) :
    ‖finiteCorrelation Finset.univ f u‖ ^ 2 =
      𝔼 h, (finiteCorrelation Finset.univ
        (multiplicativeDerivative f h) (multiplicativeDerivative u h)).re := by
  calc
    _ = (gowersMoment 1 (fun x => f x * star (u x))).re := by
      rw [gowersMoment_one, mul_star_re_eq_norm_sq]
      rfl
    _ = _ := by
      rw [gowersMoment, expect_re]
      apply Finset.expect_congr rfl
      intro h _
      congr 1
      change (𝔼 x, multiplicativeDerivative (fun x => f x * star (u x)) h x) = _
      apply Finset.expect_congr rfl
      intro x _
      simp only [multiplicativeDerivative, star_mul, star_star]
      ring

theorem correlation_sq_le_expect_norm_derivative (f u : H → ℂ) :
    ‖finiteCorrelation Finset.univ f u‖ ^ 2 ≤
      𝔼 h, ‖finiteCorrelation Finset.univ
        (multiplicativeDerivative f h) (multiplicativeDerivative u h)‖ := by
  rw [correlation_sq_eq_expect_derivative]
  exact Finset.expect_le_expect (fun _ _ => Complex.re_le_norm _)

theorem norm_derivativeCorrelation_le (f u : H → ℂ) {B : ℝ}
    (hf : ∀ x, ‖f x‖ ≤ 1) (hu : ∀ x, ‖u x‖ ≤ B) (h : H) :
    ‖finiteCorrelation Finset.univ
      (multiplicativeDerivative f h) (multiplicativeDerivative u h)‖ ≤ B ^ 2 := by
  apply norm_finiteCorrelation_le Finset.univ_nonempty
  · intro x _
    simpa only [multiplicativeDerivative, norm_mul, norm_star, one_mul] using
      mul_le_mul (hf x) (hf (x + h)) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  · intro x _
    have hB : 0 ≤ B := (norm_nonneg (u x)).trans (hu x)
    simpa only [multiplicativeDerivative, norm_mul, norm_star, pow_two] using
      mul_le_mul (hu x) (hu (x + h)) (norm_nonneg _) hB

theorem density_correlating_derivatives (f u : H → ℂ) {ρ B : ℝ}
    (hρ : 0 ≤ ρ) (hB : 0 < B) (hf : ∀ x, ‖f x‖ ≤ 1) (hu : ∀ x, ‖u x‖ ≤ B)
    (hcorr : ρ ≤ ‖finiteCorrelation Finset.univ f u‖) :
    ρ ^ 2 / (2 * B ^ 2) ≤
      𝔼 h, if ρ ^ 2 / 2 ≤ ‖finiteCorrelation Finset.univ
        (multiplicativeDerivative f h) (multiplicativeDerivative u h)‖ then (1 : ℝ) else 0 := by
  apply density_large_values_of_expect _ (sq_nonneg ρ) (sq_pos_of_pos hB)
    (norm_derivativeCorrelation_le f u hf hu)
  exact (pow_le_pow_left₀ hρ hcorr 2).trans (correlation_sq_le_expect_norm_derivative f u)

end Erdos3

end

end OAI
