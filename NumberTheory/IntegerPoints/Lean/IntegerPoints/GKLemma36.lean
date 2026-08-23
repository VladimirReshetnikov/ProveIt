import IntegerPoints.GKLemma32
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

/-! ### Capped reciprocal sums -/

/-- Sum capped reciprocals while measuring integer distance from the right endpoint.
The endpoint itself contributes only the cap `D`; the remaining terms form `harmonic n`. -/
theorem sum_minInv_Icc_from_right (u : ℤ → ℝ) {A B : ℤ} (n : ℕ) {D q : ℝ}
    (hA : A = B - (n : ℤ))
    (hu : ∀ ν ∈ Finset.Icc A B, ν < B →
      minInv D (u ν) ≤ q * (((B : ℝ) - (ν : ℝ))⁻¹)) :
    ∑ ν ∈ Finset.Icc A B, minInv D (u ν) ≤ D + q * (harmonic n : ℝ) := by
  have hharm : (harmonic n : ℝ) =
      ∑ j ∈ Finset.range n, (((j + 1 : ℕ) : ℝ)⁻¹) := by
    rw [harmonic, Rat.cast_sum]
    simp
  calc
    (∑ ν ∈ Finset.Icc A B, minInv D (u ν)) =
        ∑ j ∈ Finset.range (n + 1), minInv D (u (B - (j : ℤ))) := by
      rw [hA, PS.sum_Icc_eq_sum_range_rev]
    _ = minInv D (u B) +
        ∑ j ∈ Finset.range n, minInv D (u (B - ((j + 1 : ℕ) : ℤ))) := by
      rw [Finset.sum_range_succ']
      simp
      ring
    _ ≤ D + ∑ j ∈ Finset.range n, q * (((j + 1 : ℕ) : ℝ)⁻¹) := by
      refine add_le_add (minInv_le_left D (u B)) ?_
      exact Finset.sum_le_sum fun j hj => by
        have hjn : j < n := Finset.mem_range.mp hj
        have hmem : B - ((j + 1 : ℕ) : ℤ) ∈ Finset.Icc A B := by
          rw [Finset.mem_Icc]
          constructor <;> omega
        have hlt : B - ((j + 1 : ℕ) : ℤ) < B := by omega
        have hterm := hu (B - ((j + 1 : ℕ) : ℤ)) hmem hlt
        convert hterm using 1
        all_goals first | rfl | (push_cast; ring)
    _ = D + q * ∑ j ∈ Finset.range n, (((j + 1 : ℕ) : ℝ)⁻¹) := by
      rw [Finset.mul_sum]
    _ = D + q * (harmonic n : ℝ) := by rw [← hharm]

/-- Sum capped reciprocals while measuring integer distance from the left endpoint.
The endpoint itself contributes only the cap `D`; the remaining terms form `harmonic n`. -/
theorem sum_minInv_Icc_from_left (u : ℤ → ℝ) {A B : ℤ} (n : ℕ) {D q : ℝ}
    (hB : B = A + (n : ℤ))
    (hu : ∀ ν ∈ Finset.Icc A B, A < ν →
      minInv D (u ν) ≤ q * (((ν : ℝ) - (A : ℝ))⁻¹)) :
    ∑ ν ∈ Finset.Icc A B, minInv D (u ν) ≤ D + q * (harmonic n : ℝ) := by
  have hharm : (harmonic n : ℝ) =
      ∑ j ∈ Finset.range n, (((j + 1 : ℕ) : ℝ)⁻¹) := by
    rw [harmonic, Rat.cast_sum]
    simp
  calc
    (∑ ν ∈ Finset.Icc A B, minInv D (u ν)) =
        ∑ j ∈ Finset.range (n + 1), minInv D (u (A + (j : ℤ))) := by
      rw [hB, PS.sum_Icc_eq_sum_range_real]
    _ = minInv D (u A) +
        ∑ j ∈ Finset.range n, minInv D (u (A + ((j + 1 : ℕ) : ℤ))) := by
      rw [Finset.sum_range_succ']
      simp
      ring
    _ ≤ D + ∑ j ∈ Finset.range n, q * (((j + 1 : ℕ) : ℝ)⁻¹) := by
      refine add_le_add (minInv_le_left D (u A)) ?_
      exact Finset.sum_le_sum fun j hj => by
        have hjn : j < n := Finset.mem_range.mp hj
        have hmem : A + ((j + 1 : ℕ) : ℤ) ∈ Finset.Icc A B := by
          rw [Finset.mem_Icc]
          constructor <;> omega
        have hlt : A < A + ((j + 1 : ℕ) : ℤ) := by omega
        have hterm := hu (A + ((j + 1 : ℕ) : ℤ)) hmem hlt
        convert hterm using 1
        all_goals first | rfl | (push_cast; ring)
    _ = D + q * ∑ j ∈ Finset.range n, (((j + 1 : ℕ) : ℝ)⁻¹) := by
      rw [Finset.mul_sum]
    _ = D + q * (harmonic n : ℝ) := by rw [← hharm]

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

/-! ### Raw B-process estimate -/

/-- The analytic core of Lemma 3.6, before the `F,N` scale is substituted.

The three constants are absolute.  The bound deliberately retains `gkR₁` and `gkR₂`:
estimating their sums is arithmetic bookkeeping specific to a chosen derivative scale, whereas
the Poisson decomposition and stationary-phase argument are reusable. -/
theorem raw_bound :
    ∃ K₃₅ K₃₂ K₃₄ : ℝ, 0 ≤ K₃₅ ∧ 0 ≤ K₃₂ ∧ 0 ≤ K₃₄ ∧
      ∀ (a b lam₂ lam₃ lam₄ : ℝ) (f : ℝ → ℝ) (xν : ℤ → ℝ),
        0 ≤ a → a ≤ b → 0 < lam₂ → 0 < lam₃ → 0 < lam₄ → ContDiff ℝ 4 f →
        (∀ t ∈ Set.Icc a b, iteratedDeriv 2 f t ≤ -lam₂) →
        (∀ t ∈ Set.Icc a b, |iteratedDeriv 3 f t| ≤ lam₃) →
        (∀ t ∈ Set.Icc a b, |iteratedDeriv 4 f t| ≤ lam₄) →
        (∀ ν : ℤ, deriv f b ≤ ν → (ν : ℝ) ≤ deriv f a →
          xν ν ∈ Set.Icc a b ∧ deriv f (xν ν) = ν) →
        ‖(∑ n ∈ intRange a b, e (f n)) -
            ∑ ν ∈ Finset.Icc ⌈deriv f b⌉ ⌊deriv f a⌋,
              e (f (xν ν) - (ν : ℝ) * xν ν - 1 / 8) /
                ((Real.sqrt |iteratedDeriv 2 f (xν ν)| : ℝ) : ℂ)‖ ≤
          K₃₅ * Real.log ((⌊deriv f a⌋ : ℝ) - ⌈deriv f b⌉ + 4) +
            4 * K₃₂ * lam₂ ^ (-(1 : ℝ) / 2) +
            K₃₄ * ((∑ ν ∈ Finset.Icc ⌈deriv f b⌉ ⌊deriv f a⌋,
              gkR₁ lam₂ a b (xν ν)) +
                ((Finset.Icc ⌈deriv f b⌉ ⌊deriv f a⌋).card : ℝ) *
                  gkR₂ lam₂ lam₃ lam₄ a b) := by
  obtain ⟨C₃₅, h₃₅⟩ := gk_lemma35_holds
  obtain ⟨C₃₂, h₃₂⟩ := gk_lemma32_holds
  obtain ⟨C₃₄, h₃₄⟩ := gk_lemma34_neg_holds
  refine ⟨|C₃₅|, |C₃₂|, |C₃₄|, abs_nonneg _, abs_nonneg _, abs_nonneg _, ?_⟩
  intro a b lam₂ lam₃ lam₄ f xν ha hab hlam₂ hlam₃ hlam₄ hf h₂ h₃ h₄ hxν
  have hf₂ : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  have hf₃ : ContDiff ℝ 3 f := hf.of_le (by norm_num)
  have hanti : AntitoneOn (deriv f) (Set.Icc a b) :=
    deriv_antitoneOn hf₂ (fun t ht => (h₂ t ht).trans (neg_nonpos.mpr hlam₂.le))
  set α : ℝ := deriv f b with hα
  set β : ℝ := deriv f a with hβ
  have haI : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have hbI : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
  have hαβ : α ≤ β := by
    rw [hα, hβ]
    exact hanti haI hbI hab
  set A : ℤ := ⌈α⌉ with hA
  set B : ℤ := ⌊β⌋ with hB
  have hAB : A ≤ B + 1 := by
    rw [hA, hB]
    exact (Int.ceil_le_ceil hαβ).trans (Int.ceil_le_floor_add_one β)
  set H₁ : ℤ := A - 2 with hH₁
  set H₂ : ℤ := B + 2 with hH₂
  set J : Finset ℤ := Finset.Icc A B with hJ
  set I : ℤ → ℂ := fun ν => ∫ x in a..b, e (phase f ν x) with hI
  set M : ℤ → ℂ := fun ν =>
    e (f (xν ν) - (ν : ℝ) * xν ν - 1 / 8) /
      ((Real.sqrt |iteratedDeriv 2 f (xν ν)| : ℝ) : ℂ) with hM
  set S : ℂ := ∑ n ∈ intRange a b, e (f n) with hS
  set Pad : ℂ := ∑ ν ∈ Finset.Icc (A - 2) (B + 2), I ν with hPad
  set Left : ℂ := ∑ ν ∈ Finset.Icc (A - 2) (A - 1), I ν with hLeft
  set Central : ℂ := ∑ ν ∈ J, I ν with hCentral
  set Right : ℂ := ∑ ν ∈ Finset.Icc (B + 1) (B + 2), I ν with hRight
  set Main : ℂ := ∑ ν ∈ J, M ν with hMain

  have hAα : (A : ℝ) < α + 1 := by rw [hA]; exact Int.ceil_lt_add_one α
  have hβB : β < (B : ℝ) + 1 := by rw [hB]; exact Int.lt_floor_add_one β
  have hfreq : ∀ x ∈ Set.Icc a b, (H₁ : ℝ) < deriv f x ∧ deriv f x < H₂ := by
    intro x hx
    have hlo : α ≤ deriv f x := by
      rw [hα]
      exact hanti hx hbI hx.2
    have hhi : deriv f x ≤ β := by
      rw [hβ]
      exact hanti haI hx hx.1
    have hH₁cast : (H₁ : ℝ) = (A : ℝ) - 2 := by rw [hH₁]; push_cast; ring
    have hH₂cast : (H₂ : ℝ) = (B : ℝ) + 2 := by rw [hH₂]; push_cast; ring
    rw [hH₁cast, hH₂cast]
    constructor <;> linarith
  have hwidth : H₁ + 2 ≤ H₂ := by rw [hH₁, hH₂]; omega
  have hwidth_cast : (H₂ : ℝ) - H₁ = (B : ℝ) - A + 4 := by
    rw [hH₁, hH₂]
    push_cast
    ring
  have hwidth3 : (3 : ℝ) ≤ (B : ℝ) - A + 4 := by
    have hAB' : (A : ℝ) ≤ B + 1 := by exact_mod_cast hAB
    linarith
  have hlogwidth0 : 0 ≤ Real.log ((B : ℝ) - A + 4) :=
    Real.log_nonneg (by linarith)
  have hPoisson : ‖S - Pad‖ ≤ |C₃₅| * Real.log ((B : ℝ) - A + 4) := by
    have h := h₃₅ a b H₁ H₂ f ha hab hf₂ hanti hfreq hwidth
    rw [hwidth_cast] at h
    change ‖S - Pad‖ ≤ C₃₅ * Real.log ((B : ℝ) - A + 4) at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_abs_self C₃₅) hlogwidth0)

  have hIntegral (ν : ℤ) :
      ‖I ν‖ ≤ |C₃₂| * lam₂ ^ (-(1 : ℝ) / 2) := by
    have h := h₃₂ a b lam₂ (phase f ν) hab hlam₂ (phase_contDiff hf₂ ν)
      (fun t ht => by
        rw [iteratedDeriv_phase hf₂ (by norm_num) ν]
        have hneg : iteratedDeriv 2 f t < 0 := by linarith [h₂ t ht]
        rw [abs_of_neg hneg]
        linarith [h₂ t ht])
    change ‖I ν‖ ≤ C₃₂ * lam₂ ^ (-(1 : ℝ) / 2) at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_abs_self C₃₂) (by positivity))
  have hcardLeft : ((Finset.Icc (A - 2) (A - 1)).card : ℝ) = 2 := by
    calc
      ((Finset.Icc (A - 2) (A - 1)).card : ℝ) =
          (((A - 1) + 1 - (A - 2) : ℤ) : ℝ) := by
        exact_mod_cast (Int.card_Icc_of_le (A - 2) (A - 1) (by omega))
      _ = 2 := by push_cast; ring
  have hcardRight : ((Finset.Icc (B + 1) (B + 2)).card : ℝ) = 2 := by
    calc
      ((Finset.Icc (B + 1) (B + 2)).card : ℝ) =
          (((B + 2) + 1 - (B + 1) : ℤ) : ℝ) := by
        exact_mod_cast (Int.card_Icc_of_le (B + 1) (B + 2) (by omega))
      _ = 2 := by push_cast; ring
  have hLeftBound : ‖Left‖ ≤ 2 * |C₃₂| * lam₂ ^ (-(1 : ℝ) / 2) := by
    rw [hLeft]
    calc
      ‖∑ ν ∈ Finset.Icc (A - 2) (A - 1), I ν‖ ≤
          ∑ ν ∈ Finset.Icc (A - 2) (A - 1), ‖I ν‖ := norm_sum_le _ _
      _ ≤ ∑ _ν ∈ Finset.Icc (A - 2) (A - 1),
          |C₃₂| * lam₂ ^ (-(1 : ℝ) / 2) := Finset.sum_le_sum (fun ν _ => hIntegral ν)
      _ = 2 * |C₃₂| * lam₂ ^ (-(1 : ℝ) / 2) := by
        rw [Finset.sum_const, nsmul_eq_mul, hcardLeft]
        ring
  have hRightBound : ‖Right‖ ≤ 2 * |C₃₂| * lam₂ ^ (-(1 : ℝ) / 2) := by
    rw [hRight]
    calc
      ‖∑ ν ∈ Finset.Icc (B + 1) (B + 2), I ν‖ ≤
          ∑ ν ∈ Finset.Icc (B + 1) (B + 2), ‖I ν‖ := norm_sum_le _ _
      _ ≤ ∑ _ν ∈ Finset.Icc (B + 1) (B + 2),
          |C₃₂| * lam₂ ^ (-(1 : ℝ) / 2) := Finset.sum_le_sum (fun ν _ => hIntegral ν)
      _ = 2 * |C₃₂| * lam₂ ^ (-(1 : ℝ) / 2) := by
        rw [Finset.sum_const, nsmul_eq_mul, hcardRight]
        ring

  have hStationary (ν : ℤ) (hν : ν ∈ J) :
      ‖I ν - M ν‖ ≤
        |C₃₄| * (gkR₁ lam₂ a b (xν ν) + gkR₂ lam₂ lam₃ lam₄ a b) := by
    have hν' : A ≤ ν ∧ ν ≤ B := by
      have hν'' := hν
      rw [hJ, Finset.mem_Icc] at hν''
      exact hν''
    have hAν : (A : ℝ) ≤ ν := by exact_mod_cast hν'.1
    have hνB : (ν : ℝ) ≤ B := by exact_mod_cast hν'.2
    have hαν : α ≤ (ν : ℝ) := by
      exact (by simpa [hA] using Int.le_ceil α : α ≤ (A : ℝ)).trans hAν
    have hνβ : (ν : ℝ) ≤ β :=
      hνB.trans (by simpa [hB] using Int.floor_le β : (B : ℝ) ≤ β)
    obtain ⟨hxroot, hcrit⟩ := hxν ν (by simpa [hα] using hαν) (by simpa [hβ] using hνβ)
    have h := h₃₄ a b (xν ν) lam₂ lam₃ lam₄ (phase f ν) hab hlam₂ hlam₃ hlam₄
      (phase_contDiff hf ν)
      (fun t ht => by rw [iteratedDeriv_phase hf₂ (by norm_num) ν]; exact h₂ t ht)
      hxroot
      (by
        rw [deriv_phase (hf.of_le (by norm_num)) ν]
        change deriv f (xν ν) - (ν : ℝ) = 0
        rw [hcrit]
        ring)
      (fun t ht => by rw [iteratedDeriv_phase hf₃ (by norm_num) ν]; exact h₃ t ht)
      (fun t ht => by rw [iteratedDeriv_phase hf (by norm_num) ν]; exact h₄ t ht)
    have hmainPhase :
        -1 / 8 + phase f ν (xν ν) = f (xν ν) - (ν : ℝ) * xν ν - 1 / 8 := by
      unfold phase
      ring
    have hD2eq := congrFun (iteratedDeriv_phase hf₂ (by norm_num) ν) (xν ν)
    rw [hmainPhase, hD2eq] at h
    change ‖I ν - M ν‖ ≤
      C₃₄ * (gkR₁ lam₂ a b (xν ν) + gkR₂ lam₂ lam₃ lam₄ a b) at h
    have hR₁nonneg : 0 ≤ gkR₁ lam₂ a b (xν ν) := by
      unfold gkR₁
      exact add_nonneg
        (minInv_nonneg (by positivity) (mul_nonneg hlam₂.le (sub_nonneg.mpr hxroot.1)))
        (minInv_nonneg (by positivity) (mul_nonneg hlam₂.le (sub_nonneg.mpr hxroot.2)))
    have hR₂nonneg : 0 ≤ gkR₂ lam₂ lam₃ lam₄ a b := by
      unfold gkR₂
      have : 0 ≤ b - a := sub_nonneg.mpr hab
      positivity
    exact h.trans (mul_le_mul_of_nonneg_right (le_abs_self C₃₄)
      (add_nonneg hR₁nonneg hR₂nonneg))
  have hCentralBound : ‖Central - Main‖ ≤
      |C₃₄| * ((∑ ν ∈ J, gkR₁ lam₂ a b (xν ν)) +
        (J.card : ℝ) * gkR₂ lam₂ lam₃ lam₄ a b) := by
    rw [hCentral, hMain, ← Finset.sum_sub_distrib]
    calc
      ‖∑ ν ∈ J, (I ν - M ν)‖ ≤ ∑ ν ∈ J, ‖I ν - M ν‖ := norm_sum_le _ _
      _ ≤ ∑ ν ∈ J, |C₃₄| *
          (gkR₁ lam₂ a b (xν ν) + gkR₂ lam₂ lam₃ lam₄ a b) :=
        Finset.sum_le_sum (fun ν hν => hStationary ν hν)
      _ = |C₃₄| * ((∑ ν ∈ J, gkR₁ lam₂ a b (xν ν)) +
          (J.card : ℝ) * gkR₂ lam₂ lam₃ lam₄ a b) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]

  have hPadSplit : Pad = Left + (Central + Right) := by
    rw [hPad, hLeft, hCentral, hRight, hJ]
    exact sum_Icc_expand_two I hAB
  have hdecomp : S - Main = (S - Pad) + Left + (Central - Main) + Right := by
    rw [hPadSplit]
    ring
  change ‖S - Main‖ ≤
    |C₃₅| * Real.log ((B : ℝ) - A + 4) +
      4 * |C₃₂| * lam₂ ^ (-(1 : ℝ) / 2) +
      |C₃₄| * ((∑ ν ∈ J, gkR₁ lam₂ a b (xν ν)) +
        (J.card : ℝ) * gkR₂ lam₂ lam₃ lam₄ a b)
  rw [hdecomp]
  calc
    ‖(S - Pad) + Left + (Central - Main) + Right‖ ≤
        ‖S - Pad‖ + ‖Left‖ + ‖Central - Main‖ + ‖Right‖ := by
      calc
        _ ≤ ‖(S - Pad) + Left + (Central - Main)‖ + ‖Right‖ := norm_add_le _ _
        _ ≤ (‖(S - Pad) + Left‖ + ‖Central - Main‖) + ‖Right‖ := by
          gcongr
          exact norm_add_le _ _
        _ ≤ (‖S - Pad‖ + ‖Left‖ + ‖Central - Main‖) + ‖Right‖ := by
          gcongr
          exact norm_add_le _ _
    _ ≤ (|C₃₅| * Real.log ((B : ℝ) - A + 4) +
          2 * |C₃₂| * lam₂ ^ (-(1 : ℝ) / 2)) +
        |C₃₄| * ((∑ ν ∈ J, gkR₁ lam₂ a b (xν ν)) +
          (J.card : ℝ) * gkR₂ lam₂ lam₃ lam₄ a b) +
        2 * |C₃₂| * lam₂ ^ (-(1 : ℝ) / 2) := by
      exact add_le_add (add_le_add (add_le_add hPoisson hLeftBound) hCentralBound) hRightBound
    _ = |C₃₅| * Real.log ((B : ℝ) - A + 4) +
        4 * |C₃₂| * lam₂ ^ (-(1 : ℝ) / 2) +
        |C₃₄| * ((∑ ν ∈ J, gkR₁ lam₂ a b (xν ν)) +
          (J.card : ℝ) * gkR₂ lam₂ lam₃ lam₄ a b) := by ring

end GK36

end LeanProofs.IntegerPoints
