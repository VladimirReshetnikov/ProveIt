import IntegerPoints.GKLemma34
import IntegerPoints.GKLemma35

/-!
# Graham–Kolesnik, Lemma 3.6 (B-process asymptotic): reusable foundations

This module develops the proof of Graham–Kolesnik Lemma 3.6.  The first layer records the
structural facts shared by the raw Poisson/stationary-phase estimate and the later B-process:

* subtracting the integer-frequency linear phase preserves all derivatives of order at least two;
* negative second derivative makes `f'` antitone, with a quantitative endpoint-drop bound;
* the Poisson interval with two padding frequencies at each end splits exactly into two outer
  two-point intervals and the stationary interval; and
* the number of stationary frequencies is bounded directly by the derivative span.

The interval and cardinality statements deliberately cover the one-past case
`⌈α⌉ = ⌊β⌋ + 1`, where the stationary interval is empty.
-/

open Real Finset

namespace LeanProofs.IntegerPoints

namespace GK36

/-- The phase `f(x) - νx` occurring after Poisson summation. -/
noncomputable def phase (f : ℝ → ℝ) (ν : ℤ) (x : ℝ) : ℝ := f x - (ν : ℝ) * x

/-- Subtracting a linear phase preserves the differentiability class of `f`. -/
theorem phase_contDiff {n : WithTop ℕ∞} {f : ℝ → ℝ} (hf : ContDiff ℝ n f) (ν : ℤ) :
    ContDiff ℝ n (phase f ν) := by
  unfold phase
  exact hf.sub (contDiff_const.mul contDiff_id)

/-- The first derivative of `f(x) - νx` is `f'(x) - ν`. -/
theorem deriv_phase {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (ν : ℤ) :
    deriv (phase f ν) = fun x => deriv f x - (ν : ℝ) := by
  funext x
  unfold phase
  simpa only [id_eq, deriv_const_mul_id] using
    (deriv_fun_sub hf.differentiable_one.differentiableAt
      (differentiableAt_id.const_mul (ν : ℝ)))

/-- A linear phase has no effect on any iterated derivative of order at least two. -/
theorem iteratedDeriv_phase {n : ℕ} {f : ℝ → ℝ} (hf : ContDiff ℝ n f) (hn : 2 ≤ n)
    (ν : ℤ) : iteratedDeriv n (phase f ν) = iteratedDeriv n f := by
  have hlin : ContDiff ℝ n (fun x : ℝ => (ν : ℝ) * x) := contDiff_const.mul contDiff_id
  funext x
  change iteratedDeriv n (f - fun y : ℝ => (ν : ℝ) * y) x = iteratedDeriv n f x
  rw [iteratedDeriv_sub hf.contDiffAt hlin.contDiffAt]
  have hlinear :
      iteratedDeriv n (fun y : ℝ => (ν : ℝ) * y) x =
        (ν : ℝ) * iteratedDeriv n id x := by
    simpa only [id_eq] using
      (iteratedDeriv_const_mul_field (n := n) (x := x) (ν : ℝ) id)
  rw [hlinear, iteratedDeriv_id]
  simp [show n ≠ 0 by omega, show n ≠ 1 by omega]

/-- A nonpositive second derivative makes the first derivative antitone on an interval. -/
theorem deriv_antitoneOn {a b : ℝ} {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (h2 : ∀ x ∈ Set.Icc a b, iteratedDeriv 2 f x ≤ 0) :
    AntitoneOn (deriv f) (Set.Icc a b) := by
  have hf1 : ContDiff ℝ 1 (deriv f) :=
    (contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1 + 1) f from hf)).2.2
  refine antitoneOn_of_deriv_nonpos (convex_Icc a b) hf1.continuous.continuousOn
    (hf1.differentiable one_ne_zero).differentiableOn ?_
  intro x hx
  rw [← GK34.iteratedDeriv_two]
  exact h2 x (interior_subset hx)

/-- If `-f'' ≤ M`, the first derivative drops by at most `M` times the distance. -/
theorem deriv_sub_deriv_le {a b M x y : ℝ} {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hM : ∀ z ∈ Set.Icc a b, -iteratedDeriv 2 f z ≤ M)
    (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b) (hxy : x ≤ y) :
    deriv f x - deriv f y ≤ M * (y - x) := by
  have hf1 : ContDiff ℝ 1 (deriv f) :=
    (contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1 + 1) f from hf)).2.2
  have hmv := Convex.mul_sub_le_image_sub_of_le_deriv (convex_Icc a b)
    hf1.continuous.continuousOn
    (hf1.differentiable one_ne_zero).differentiableOn
    (C := -M)
    (fun z hz => by
      have hzI : z ∈ Set.Icc a b := interior_subset hz
      rw [← GK34.iteratedDeriv_two]
      linarith [hM z hzI])
    x hx y hy hxy
  linarith

/-- The derivative-drop estimate specialized to the two sides of an interior point. -/
theorem deriv_endpoint_gaps {a b M x : ℝ} {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hM : ∀ z ∈ Set.Icc a b, -iteratedDeriv 2 f z ≤ M) (hab : a ≤ b)
    (hx : x ∈ Set.Icc a b) :
    deriv f a - deriv f x ≤ M * (x - a) ∧
      deriv f x - deriv f b ≤ M * (b - x) := by
  have haI : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have hbI : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
  exact ⟨deriv_sub_deriv_le hf hM haI hx hx.1,
    deriv_sub_deriv_le hf hM hx hbI hx.2⟩

/-- Padding the stationary interval by two frequencies on each side gives three exact pieces. -/
theorem Icc_expand_two {A B : ℤ} (hAB : A ≤ B + 1) :
    Finset.Icc (A - 2) (B + 2) =
      Finset.Icc (A - 2) (A - 1) ∪
        (Finset.Icc A B ∪ Finset.Icc (B + 1) (B + 2)) := by
  ext x
  simp only [Finset.mem_Icc, Finset.mem_union]
  omega

/-- The left padding interval is disjoint from the stationary interval. -/
theorem disjoint_left_middle (A B : ℤ) :
    Disjoint (Finset.Icc (A - 2) (A - 1)) (Finset.Icc A B) := by
  rw [Finset.disjoint_left]
  intro x hxL hxM
  simp only [Finset.mem_Icc] at hxL hxM
  omega

/-- The stationary interval is disjoint from the right padding interval. -/
theorem disjoint_middle_right (A B : ℤ) :
    Disjoint (Finset.Icc A B) (Finset.Icc (B + 1) (B + 2)) := by
  rw [Finset.disjoint_left]
  intro x hxM hxR
  simp only [Finset.mem_Icc] at hxM hxR
  omega

/-- Under the one-past condition, the two padding intervals are disjoint. -/
theorem disjoint_left_right {A B : ℤ} (hAB : A ≤ B + 1) :
    Disjoint (Finset.Icc (A - 2) (A - 1)) (Finset.Icc (B + 1) (B + 2)) := by
  rw [Finset.disjoint_left]
  intro x hxL hxR
  simp only [Finset.mem_Icc] at hxL hxR
  omega

/-- Sum form of `Icc_expand_two`, including an empty stationary interval. -/
theorem sum_Icc_expand_two {R : Type*} [AddCommMonoid R] (F : ℤ → R) {A B : ℤ}
    (hAB : A ≤ B + 1) :
    ∑ ν ∈ Finset.Icc (A - 2) (B + 2), F ν =
      (∑ ν ∈ Finset.Icc (A - 2) (A - 1), F ν) +
        ((∑ ν ∈ Finset.Icc A B, F ν) +
          ∑ ν ∈ Finset.Icc (B + 1) (B + 2), F ν) := by
  rw [Icc_expand_two hAB]
  have hLM := disjoint_left_middle A B
  have hLR := disjoint_left_right hAB
  have hMR := disjoint_middle_right A B
  have hL_MR : Disjoint (Finset.Icc (A - 2) (A - 1))
      (Finset.Icc A B ∪ Finset.Icc (B + 1) (B + 2)) :=
    Finset.disjoint_union_right.mpr ⟨hLM, hLR⟩
  rw [Finset.sum_union hL_MR, Finset.sum_union hMR]

/-- The stationary integer interval has at most derivative span plus one elements. -/
theorem card_Icc_ceil_floor_le {α β : ℝ} (hαβ : α ≤ β) :
    ((Finset.Icc ⌈α⌉ ⌊β⌋).card : ℝ) ≤ β - α + 1 := by
  have hAB : ⌈α⌉ ≤ ⌊β⌋ + 1 :=
    (Int.ceil_le_ceil hαβ).trans (Int.ceil_le_floor_add_one β)
  calc
    ((Finset.Icc ⌈α⌉ ⌊β⌋).card : ℝ) = ((⌊β⌋ + 1 - ⌈α⌉ : ℤ) : ℝ) := by
      exact_mod_cast (Int.card_Icc_of_le ⌈α⌉ ⌊β⌋ hAB)
    _ = (⌊β⌋ : ℝ) + 1 - (⌈α⌉ : ℝ) := by push_cast; ring
    _ ≤ β - α + 1 := by linarith [Int.floor_le β, Int.le_ceil α]

/-! ### Scale normalization -/

/-- The inverse square root of the curvature scale `c F N⁻²` has the expected
dimension `c⁻¹ᐟ² F⁻¹ᐟ² N`. -/
theorem inverse_sqrt_scale {c F N : ℝ} (hc : 0 < c) (hF : 0 < F) (hN : 0 < N) :
    (c * F * N ^ (-(2 : ℝ))) ^ (-(1 : ℝ) / 2) =
      c ^ (-(1 : ℝ) / 2) * F ^ (-(1 : ℝ) / 2) * N := by
  rw [Real.mul_rpow (mul_nonneg hc.le hF.le) (Real.rpow_nonneg hN.le _),
    Real.mul_rpow hc.le hF.le, ← Real.rpow_mul hN.le]
  norm_num

/-- The fourth-derivative contribution in `gkR₂` loses every power of `N`. -/
theorem fourth_scale {c₁ c₄ F N : ℝ} (hc₁ : 0 < c₁) (hF : 0 < F) (hN : 0 < N) :
    (c₄ * F * N ^ (-(4 : ℝ))) *
        (c₁ * F * N ^ (-(2 : ℝ))) ^ (-(2 : ℝ)) =
      (c₄ * c₁ ^ (-(2 : ℝ))) * F ^ (-(1 : ℝ)) := by
  have hc₁F0 : 0 ≤ c₁ * F := mul_nonneg hc₁.le hF.le
  have hNm2_0 : 0 ≤ N ^ (-(2 : ℝ)) := Real.rpow_nonneg hN.le _
  have hN22 : (N ^ (-(2 : ℝ))) ^ (-(2 : ℝ)) = N ^ (4 : ℝ) := by
    rw [← Real.rpow_mul hN.le]
    norm_num
  have hF12 : F * F ^ (-(2 : ℝ)) = F ^ (-(1 : ℝ)) := by
    calc
      F * F ^ (-(2 : ℝ)) = F ^ (1 : ℝ) * F ^ (-(2 : ℝ)) := by rw [Real.rpow_one]
      _ = F ^ ((1 : ℝ) + -(2 : ℝ)) := by rw [← Real.rpow_add hF]
      _ = F ^ (-(1 : ℝ)) := by congr 1; norm_num
  have hN44 : N ^ (-(4 : ℝ)) * N ^ (4 : ℝ) = 1 := by
    rw [← Real.rpow_add hN]
    norm_num
  rw [Real.mul_rpow hc₁F0 hNm2_0, Real.mul_rpow hc₁.le hF.le, hN22]
  calc
    c₄ * F * N ^ (-(4 : ℝ)) *
          (c₁ ^ (-(2 : ℝ)) * F ^ (-(2 : ℝ)) * N ^ (4 : ℝ)) =
        (c₄ * c₁ ^ (-(2 : ℝ))) * (F * F ^ (-(2 : ℝ))) *
          (N ^ (-(4 : ℝ)) * N ^ (4 : ℝ)) := by ring
    _ = (c₄ * c₁ ^ (-(2 : ℝ))) * F ^ (-(1 : ℝ)) := by
      rw [hF12, hN44, mul_one]

/-- The squared third-derivative contribution in `gkR₂` likewise loses every power of `N`. -/
theorem third_scale {c₁ c₃ F N : ℝ} (hc₁ : 0 < c₁) (hF : 0 < F) (hN : 0 < N) :
    (c₃ * F * N ^ (-(3 : ℝ))) ^ 2 *
        (c₁ * F * N ^ (-(2 : ℝ))) ^ (-(3 : ℝ)) =
      (c₃ ^ 2 * c₁ ^ (-(3 : ℝ))) * F ^ (-(1 : ℝ)) := by
  have hc₁F0 : 0 ≤ c₁ * F := mul_nonneg hc₁.le hF.le
  have hNm2_0 : 0 ≤ N ^ (-(2 : ℝ)) := Real.rpow_nonneg hN.le _
  have hN32 : (N ^ (-(3 : ℝ))) ^ 2 = N ^ (-(6 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
    norm_num
  have hN23 : (N ^ (-(2 : ℝ))) ^ (-(3 : ℝ)) = N ^ (6 : ℝ) := by
    rw [← Real.rpow_mul hN.le]
    norm_num
  have hF23 : F ^ 2 * F ^ (-(3 : ℝ)) = F ^ (-(1 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hF]
    norm_num
  have hN66 : N ^ (-(6 : ℝ)) * N ^ (6 : ℝ) = 1 := by
    rw [← Real.rpow_add hN]
    norm_num
  simp only [mul_pow]
  rw [hN32, Real.mul_rpow hc₁F0 hNm2_0, Real.mul_rpow hc₁.le hF.le, hN23]
  calc
    (c₃ ^ 2 * F ^ 2 * N ^ (-(6 : ℝ))) *
          (c₁ ^ (-(3 : ℝ)) * F ^ (-(3 : ℝ)) * N ^ (6 : ℝ)) =
        (c₃ ^ 2 * c₁ ^ (-(3 : ℝ))) * (F ^ 2 * F ^ (-(3 : ℝ))) *
          (N ^ (-(6 : ℝ)) * N ^ (6 : ℝ)) := by ring
    _ = (c₃ ^ 2 * c₁ ^ (-(3 : ℝ))) * F ^ (-(1 : ℝ)) := by
      rw [hF23, hN66, mul_one]

/-- For `F ≥ 1`, the scale `N/F` is absorbed by `F⁻¹ᐟ² N`. -/
theorem div_le_inverse_sqrt_mul {F N : ℝ} (hF1 : 1 ≤ F) (hN : 0 ≤ N) :
    N / F ≤ F ^ (-(1 : ℝ) / 2) * N := by
  have hpow : F ^ (-(1 : ℝ)) ≤ F ^ (-(1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hF1 (by norm_num)
  calc
    N / F = F ^ (-(1 : ℝ)) * N := by rw [Real.rpow_neg_one]; ring
    _ ≤ F ^ (-(1 : ℝ) / 2) * N := mul_le_mul_of_nonneg_right hpow hN

/-! ### Logarithmic normalization -/

/-- Normalize a logarithm against `log (y + 2)`.  This form is tailored to a widened
frequency interval whose width is at most `M (y + 2)`. -/
theorem log_normalize {y M H : ℝ} (hy : 0 < y) (hM2 : 2 ≤ M) (hH0 : 0 < H)
    (hHM : H ≤ M * (y + 2)) :
    Real.log H ≤ (1 + Real.log M / Real.log 2) * Real.log (y + 2) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hM0 : 0 < M := lt_of_lt_of_le (by norm_num) hM2
  have hy2 : 0 < y + 2 := by linarith
  have hlogM0 : 0 ≤ Real.log M := Real.log_nonneg (by linarith)
  have hlog2_le : Real.log 2 ≤ Real.log (y + 2) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hratio : 1 ≤ Real.log (y + 2) / Real.log 2 := by
    rw [le_div_iff₀ hlog2]
    simpa using hlog2_le
  have hlogM_absorb :
      Real.log M ≤ Real.log M / Real.log 2 * Real.log (y + 2) := by
    calc
      Real.log M = Real.log M * 1 := by ring
      _ ≤ Real.log M * (Real.log (y + 2) / Real.log 2) :=
        mul_le_mul_of_nonneg_left hratio hlogM0
      _ = Real.log M / Real.log 2 * Real.log (y + 2) := by ring
  calc
    Real.log H ≤ Real.log (M * (y + 2)) := Real.log_le_log hH0 hHM
    _ = Real.log M + Real.log (y + 2) := Real.log_mul hM0.ne' hy2.ne'
    _ ≤ Real.log M / Real.log 2 * Real.log (y + 2) + Real.log (y + 2) :=
      add_le_add hlogM_absorb le_rfl
    _ = (1 + Real.log M / Real.log 2) * Real.log (y + 2) := by ring

end GK36

end LeanProofs.IntegerPoints
