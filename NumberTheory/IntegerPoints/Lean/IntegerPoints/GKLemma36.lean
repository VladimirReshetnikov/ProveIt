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

/-- Sum the `gkR₁` errors once the two derivative-to-endpoint gap estimates are known.
This includes the empty one-past interval `A = B + 1`. -/
theorem sum_gkR₁_le_of_gaps {a b lam₂ M₂ : ℝ} {A B : ℤ} (xν : ℤ → ℝ)
    (hlam₂ : 0 < lam₂) (hM₂ : 0 < M₂)
    (hgapLeft : ∀ ν ∈ Finset.Icc A B,
      (B : ℝ) - (ν : ℝ) ≤ M₂ * (xν ν - a))
    (hgapRight : ∀ ν ∈ Finset.Icc A B,
      (ν : ℝ) - (A : ℝ) ≤ M₂ * (b - xν ν)) :
    ∑ ν ∈ Finset.Icc A B, gkR₁ lam₂ a b (xν ν) ≤
      2 * lam₂ ^ (-(1 : ℝ) / 2) +
        2 * (M₂ / lam₂) * (harmonic (B - A).toNat : ℝ) := by
  by_cases hnonempty : A ≤ B
  · set n : ℕ := (B - A).toNat with hn
    have hBA0 : 0 ≤ B - A := sub_nonneg.mpr hnonempty
    have hnCast : (n : ℤ) = B - A := by
      rw [hn, Int.toNat_of_nonneg hBA0]
    have hB : B = A + (n : ℤ) := by omega
    have hA : A = B - (n : ℤ) := by omega
    set D : ℝ := lam₂ ^ (-(1 : ℝ) / 2) with hD
    set q : ℝ := M₂ / lam₂ with hq
    have hpointLeft : ∀ ν ∈ Finset.Icc A B, ν < B →
        minInv D (lam₂ * (xν ν - a)) ≤ q * (((B : ℝ) - (ν : ℝ))⁻¹) := by
      intro ν hν hνB
      have hνB' : (ν : ℝ) < B := by exact_mod_cast hνB
      have hj : 0 < (B : ℝ) - (ν : ℝ) := by linarith
      have hdist : ((B : ℝ) - (ν : ℝ)) / M₂ ≤ xν ν - a :=
        (div_le_iff₀ hM₂).2 (by simpa [mul_comm] using hgapLeft ν hν)
      have hdist0 : 0 < xν ν - a := (div_pos hj hM₂).trans_le hdist
      have hsmall : 0 < lam₂ * (((B : ℝ) - (ν : ℝ)) / M₂) := by positivity
      calc
        minInv D (lam₂ * (xν ν - a)) ≤ 1 / (lam₂ * (xν ν - a)) :=
          minInv_le_inv (mul_pos hlam₂ hdist0)
        _ ≤ 1 / (lam₂ * (((B : ℝ) - (ν : ℝ)) / M₂)) :=
          one_div_le_one_div_of_le hsmall (mul_le_mul_of_nonneg_left hdist hlam₂.le)
        _ = q * (((B : ℝ) - (ν : ℝ))⁻¹) := by
          rw [hq]
          field_simp [hlam₂.ne', hM₂.ne', hj.ne']
    have hpointRight : ∀ ν ∈ Finset.Icc A B, A < ν →
        minInv D (lam₂ * (b - xν ν)) ≤ q * (((ν : ℝ) - (A : ℝ))⁻¹) := by
      intro ν hν hAν
      have hAν' : (A : ℝ) < ν := by exact_mod_cast hAν
      have hj : 0 < (ν : ℝ) - (A : ℝ) := by linarith
      have hdist : ((ν : ℝ) - (A : ℝ)) / M₂ ≤ b - xν ν :=
        (div_le_iff₀ hM₂).2 (by simpa [mul_comm] using hgapRight ν hν)
      have hdist0 : 0 < b - xν ν := (div_pos hj hM₂).trans_le hdist
      have hsmall : 0 < lam₂ * (((ν : ℝ) - (A : ℝ)) / M₂) := by positivity
      calc
        minInv D (lam₂ * (b - xν ν)) ≤ 1 / (lam₂ * (b - xν ν)) :=
          minInv_le_inv (mul_pos hlam₂ hdist0)
        _ ≤ 1 / (lam₂ * (((ν : ℝ) - (A : ℝ)) / M₂)) :=
          one_div_le_one_div_of_le hsmall (mul_le_mul_of_nonneg_left hdist hlam₂.le)
        _ = q * (((ν : ℝ) - (A : ℝ))⁻¹) := by
          rw [hq]
          field_simp [hlam₂.ne', hM₂.ne', hj.ne']
    have hleft := sum_minInv_Icc_from_right
      (u := fun ν => lam₂ * (xν ν - a)) (A := A) (B := B) n hA hpointLeft
    have hright := sum_minInv_Icc_from_left
      (u := fun ν => lam₂ * (b - xν ν)) (A := A) (B := B) n hB hpointRight
    unfold gkR₁
    rw [Finset.sum_add_distrib]
    calc
      _ ≤ (D + q * (harmonic n : ℝ)) + (D + q * (harmonic n : ℝ)) :=
        add_le_add hleft hright
      _ = 2 * lam₂ ^ (-(1 : ℝ) / 2) +
          2 * (M₂ / lam₂) * (harmonic (B - A).toNat : ℝ) := by
        rw [hD, hq, hn]
        ring
  · rw [Finset.Icc_eq_empty hnonempty]
    simp
    have hh : 0 ≤ (harmonic (B - A).toNat : ℝ) := by
      rw [harmonic, Rat.cast_sum]
      positivity
    exact add_nonneg (by positivity)
      (mul_nonneg (mul_nonneg (by norm_num) (div_nonneg hM₂.le hlam₂.le)) hh)

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

/-- Normalize a harmonic number against `log (y + 2)` through an auxiliary width `H`.
The proof treats `n = 0` separately because `Real.log_le_log` requires a positive left input. -/
theorem harmonic_normalize {n : ℕ} {y M H : ℝ} (hy : 0 < y) (hM2 : 2 ≤ M)
    (hH0 : 0 < H) (hH1 : 1 ≤ H) (hHM : H ≤ M * (y + 2)) (hnH : (n : ℝ) ≤ H) :
    (harmonic n : ℝ) ≤
      (1 / Real.log 2 + (1 + Real.log M / Real.log 2)) * Real.log (y + 2) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2L : Real.log 2 ≤ Real.log (y + 2) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hlogH : Real.log H ≤
      (1 + Real.log M / Real.log 2) * Real.log (y + 2) :=
    log_normalize hy hM2 hH0 hHM
  have hlognH : Real.log (n : ℝ) ≤ Real.log H := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · rw [hn, Nat.cast_zero, Real.log_zero]
      exact Real.log_nonneg hH1
    · exact Real.log_le_log (by exact_mod_cast hn) hnH
  have hone : (1 : ℝ) ≤ 1 / Real.log 2 * Real.log (y + 2) := by
    calc
      (1 : ℝ) ≤ Real.log (y + 2) / Real.log 2 := by
        rw [le_div_iff₀ hlog2]
        simpa using hlog2L
      _ = 1 / Real.log 2 * Real.log (y + 2) := by ring
  calc
    (harmonic n : ℝ) ≤ 1 + Real.log n := harmonic_le_one_add_log n
    _ ≤ 1 / Real.log 2 * Real.log (y + 2) +
        (1 + Real.log M / Real.log 2) * Real.log (y + 2) :=
      add_le_add hone (hlognH.trans hlogH)
    _ = (1 / Real.log 2 + (1 + Real.log M / Real.log 2)) *
        Real.log (y + 2) := by ring

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

open GK36 in
set_option maxHeartbeats 2000000 in
/-- **Graham–Kolesnik, Lemma 3.6** (the `B`-process transformation). -/
theorem gk_lemma36_holds : gk_lemma36 := by
  obtain ⟨K₃₅, K₃₂, K₃₄, hK₃₅, hK₃₂, hK₃₄, hraw⟩ := raw_bound
  intro c₁ c₂ c₃ c₄ hc₁ hc₂ hc₃ hc₄
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set r : ℝ := c₁ ^ (-(1 : ℝ) / 2) with hr
  set q : ℝ := c₂ / c₁ with hq
  set d : ℝ := c₄ * c₁ ^ (-(2 : ℝ)) + c₃ ^ 2 * c₁ ^ (-(3 : ℝ)) with hd
  set W : ℝ := max c₂ 2 with hW
  set Klog : ℝ := 1 + Real.log W / Real.log 2 with hKlog
  set Kharm : ℝ := 1 / Real.log 2 + Klog with hKharm
  set Alog : ℝ := K₃₅ * Klog + K₃₄ * (2 * q * Kharm + d * c₂ / Real.log 2) with hAlog
  set Atime : ℝ := 4 * K₃₂ * r + K₃₄ * (2 * r + d) with hAtime
  set Clarge : ℝ := Alog + Atime with hClarge
  set Csmall : ℝ := 3 + r + c₂ * r / Real.log 2 with hCsmall
  set C : ℝ := Clarge + Csmall with hC
  have hr0 : 0 < r := by rw [hr]; positivity
  have hq0 : 0 < q := by rw [hq]; positivity
  have hd0 : 0 < d := by rw [hd]; positivity
  have hW2 : (2 : ℝ) ≤ W := by rw [hW]; exact le_max_right _ _
  have hlogW0 : 0 ≤ Real.log W := Real.log_nonneg (by linarith)
  have hKlog0 : 0 ≤ Klog := by
    rw [hKlog]
    exact add_nonneg zero_le_one (div_nonneg hlogW0 hlog2.le)
  have hKharm0 : 0 ≤ Kharm := by
    rw [hKharm]
    exact add_nonneg (div_nonneg zero_le_one hlog2.le) hKlog0
  have hAlog0 : 0 ≤ Alog := by rw [hAlog]; positivity
  have hAtime0 : 0 ≤ Atime := by rw [hAtime]; positivity
  have hClarge0 : 0 ≤ Clarge := by rw [hClarge]; positivity
  have hCsmall0 : 0 ≤ Csmall := by rw [hCsmall]; positivity
  have hC0 : 0 ≤ C := by rw [hC]; positivity
  refine ⟨C, ?_⟩
  intro N F a b f xν hN hF hNa hab hb2N hf h₂ h₃ h₄ hxν

  set lam₂ : ℝ := c₁ * F * N ^ (-(2 : ℝ)) with hlam₂
  set lam₃ : ℝ := c₃ * F * N ^ (-(3 : ℝ)) with hlam₃
  set lam₄ : ℝ := c₄ * F * N ^ (-(4 : ℝ)) with hlam₄
  set M₂ : ℝ := c₂ * F * N ^ (-(2 : ℝ)) with hM₂
  set y : ℝ := F * N⁻¹ with hy
  set L : ℝ := Real.log (y + 2) with hL
  set T : ℝ := F ^ (-(1 : ℝ) / 2) * N with hT
  set s : ℝ := lam₂ ^ (-(1 : ℝ) / 2) with hs
  have hlam₂0 : 0 < lam₂ := by rw [hlam₂]; positivity
  have hlam₃0 : 0 < lam₃ := by rw [hlam₃]; positivity
  have hlam₄0 : 0 < lam₄ := by rw [hlam₄]; positivity
  have hM₂0 : 0 < M₂ := by rw [hM₂]; positivity
  have hy0 : 0 < y := by rw [hy]; positivity
  have hL0 : 0 ≤ L := by
    rw [hL]
    exact Real.log_nonneg (by linarith)
  have hT0 : 0 < T := by rw [hT]; positivity
  have hs0 : 0 < s := by rw [hs]; positivity
  have hsScale : s = r * T := by
    rw [hs, hlam₂, hr, hT]
    simpa only [mul_assoc] using inverse_sqrt_scale hc₁ hF hN
  have hratio : M₂ / lam₂ = q := by
    rw [div_eq_iff hlam₂0.ne', hM₂, hq, hlam₂]
    field_simp [hc₁.ne']
  have hlog2L : Real.log 2 ≤ L := by
    rw [hL]
    exact Real.log_le_log (by norm_num) (by linarith [hy0])
  have honeL : (1 : ℝ) ≤ L / Real.log 2 := by
    rw [le_div_iff₀ hlog2]
    simpa using hlog2L

  have hf₂ : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  have hMbound : ∀ z ∈ Set.Icc a b, -iteratedDeriv 2 f z ≤ M₂ := by
    intro z hz
    simpa [hM₂] using (h₂ z hz).2
  have hanti : AntitoneOn (deriv f) (Set.Icc a b) :=
    deriv_antitoneOn hf₂ (fun z hz => by linarith [(h₂ z hz).1])
  set α : ℝ := deriv f b with hα
  set β : ℝ := deriv f a with hβ
  have haI : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have hbI : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
  have hαβ : α ≤ β := by
    rw [hα, hβ]
    exact hanti haI hbI hab
  set A₀ : ℤ := ⌈α⌉ with hA₀
  set B₀ : ℤ := ⌊β⌋ with hB₀
  have hAB : A₀ ≤ B₀ + 1 := by
    rw [hA₀, hB₀]
    exact (Int.ceil_le_ceil hαβ).trans (Int.ceil_le_floor_add_one β)
  set J : Finset ℤ := Finset.Icc A₀ B₀ with hJ
  set S : ℂ := ∑ n ∈ intRange a b, e (f n) with hS
  set Main : ℂ := ∑ ν ∈ J,
    e (f (xν ν) - (ν : ℝ) * xν ν - 1 / 8) /
      ((Real.sqrt |iteratedDeriv 2 f (xν ν)| : ℝ) : ℂ) with hMain
  have hxJ : ∀ ν ∈ J, xν ν ∈ Set.Icc a b ∧ deriv f (xν ν) = ν := by
    intro ν hν
    have hν' := hν
    rw [hJ, Finset.mem_Icc] at hν'
    apply hxν ν
    · calc
        deriv f b = α := hα.symm
        _ ≤ (A₀ : ℝ) := by rw [hA₀]; exact Int.le_ceil _
        _ ≤ (ν : ℝ) := by exact_mod_cast hν'.1
    · calc
        (ν : ℝ) ≤ (B₀ : ℝ) := by exact_mod_cast hν'.2
        _ ≤ β := by rw [hB₀]; exact Int.floor_le _
        _ = deriv f a := hβ
  have hgapLeft : ∀ ν ∈ J,
      (B₀ : ℝ) - (ν : ℝ) ≤ M₂ * (xν ν - a) := by
    intro ν hν
    obtain ⟨hxroot, hcrit⟩ := hxJ ν hν
    have hends := deriv_endpoint_gaps hf₂ hMbound hab hxroot
    rw [hcrit] at hends
    have hBfloor : (B₀ : ℝ) ≤ deriv f a := by rw [hB₀, hβ]; exact Int.floor_le _
    linarith [hends.1]
  have hgapRight : ∀ ν ∈ J,
      (ν : ℝ) - (A₀ : ℝ) ≤ M₂ * (b - xν ν) := by
    intro ν hν
    obtain ⟨hxroot, hcrit⟩ := hxJ ν hν
    have hends := deriv_endpoint_gaps hf₂ hMbound hab hxroot
    rw [hcrit] at hends
    have hAceil : deriv f b ≤ (A₀ : ℝ) := by rw [hA₀, hα]; exact Int.le_ceil _
    linarith [hends.2]
  have hR₁raw : ∑ ν ∈ J, gkR₁ lam₂ a b (xν ν) ≤
      2 * s + 2 * (M₂ / lam₂) * (harmonic (B₀ - A₀).toNat : ℝ) := by
    rw [hJ, hs]
    exact sum_gkR₁_le_of_gaps xν hlam₂0 hM₂0
      (by simpa [hJ] using hgapLeft) (by simpa [hJ] using hgapRight)

  have hspan : β - α ≤ M₂ * (b - a) := by
    rw [hα, hβ]
    exact deriv_sub_deriv_le hf₂ hMbound haI hbI hab
  have hbaN : b - a ≤ N := by linarith
  have hNm2N : N ^ (-(2 : ℝ)) * N = N⁻¹ := by
    calc
      N ^ (-(2 : ℝ)) * N = N ^ (-(2 : ℝ)) * N ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = N ^ (-(2 : ℝ) + (1 : ℝ)) := by rw [← Real.rpow_add hN]
      _ = N ^ (-(1 : ℝ)) := by norm_num
      _ = N⁻¹ := Real.rpow_neg_one N
  have hMspan : M₂ * (b - a) ≤ c₂ * y := by
    calc
      M₂ * (b - a) ≤ M₂ * N := mul_le_mul_of_nonneg_left hbaN hM₂0.le
      _ = c₂ * y := by
        rw [hM₂, hy]
        rw [show c₂ * F * N ^ (-(2 : ℝ)) * N =
          c₂ * F * (N ^ (-(2 : ℝ)) * N) by ring, hNm2N]
        ring
  have hspanY : β - α ≤ c₂ * y := hspan.trans hMspan
  have hcardSpan : (J.card : ℝ) ≤ β - α + 1 := by
    rw [hJ, hA₀, hB₀]
    exact card_Icc_ceil_floor_le hαβ
  have hcard : (J.card : ℝ) ≤ c₂ * y + 1 := hcardSpan.trans (by linarith)

  set H : ℝ := (B₀ : ℝ) - A₀ + 4 with hH
  set n : ℕ := (B₀ - A₀).toNat with hn
  have hH3 : (3 : ℝ) ≤ H := by
    have hAB' : (A₀ : ℝ) ≤ B₀ + 1 := by exact_mod_cast hAB
    rw [hH]
    linarith
  have hH0 : 0 < H := by linarith
  have hH1 : (1 : ℝ) ≤ H := by linarith
  have hBAround : (B₀ : ℝ) - A₀ ≤ β - α := by
    rw [hA₀, hB₀]
    exact sub_le_sub (Int.floor_le β) (Int.le_ceil α)
  have hHrough : H ≤ c₂ * y + 4 := by rw [hH]; linarith
  have hc₂W : c₂ ≤ W := by rw [hW]; exact le_max_left _ _
  have hHW : H ≤ W * (y + 2) := by
    calc
      H ≤ c₂ * y + 4 := hHrough
      _ ≤ W * y + W * 2 := add_le_add
        (mul_le_mul_of_nonneg_right hc₂W hy0.le) (by nlinarith [hW2])
      _ = W * (y + 2) := by ring
  have hnH : (n : ℝ) ≤ H := by
    by_cases hBA0 : 0 ≤ B₀ - A₀
    · have hnCast : (n : ℤ) = B₀ - A₀ := by rw [hn, Int.toNat_of_nonneg hBA0]
      have hnReal := congrArg (fun z : ℤ => (z : ℝ)) hnCast
      push_cast at hnReal
      rw [hH]
      linarith
    · have hBAle : B₀ - A₀ ≤ 0 := le_of_not_ge hBA0
      have hn0 : n = 0 := by rw [hn, Int.toNat_of_nonpos hBAle]
      rw [hn0, Nat.cast_zero]
      linarith
  have hlogH : Real.log H ≤ Klog * L := by
    rw [hKlog, hL]
    exact log_normalize hy0 hW2 hH0 hHW
  have hharm : (harmonic n : ℝ) ≤ Kharm * L := by
    rw [hKharm, hL]
    exact harmonic_normalize hy0 hW2 hH0 hH1 hHW hnH
  have hR₁ : ∑ ν ∈ J, gkR₁ lam₂ a b (xν ν) ≤
      2 * r * T + (2 * q * Kharm) * L := by
    calc
      _ ≤ 2 * s + 2 * (M₂ / lam₂) * (harmonic (B₀ - A₀).toNat : ℝ) := hR₁raw
      _ = 2 * r * T + 2 * q * (harmonic n : ℝ) := by
        rw [hsScale, hratio, hn]
        ring
      _ ≤ 2 * r * T + 2 * q * (Kharm * L) := by
        have hscaled :
            2 * q * (harmonic n : ℝ) ≤ 2 * q * (Kharm * L) :=
          mul_le_mul_of_nonneg_left hharm (mul_nonneg (by norm_num) hq0.le)
        exact add_le_add le_rfl hscaled
      _ = 2 * r * T + (2 * q * Kharm) * L := by ring

  have hR₂eq : gkR₂ lam₂ lam₃ lam₄ a b = (b - a) * d / F := by
    unfold gkR₂
    calc
      (b - a) * lam₄ * lam₂ ^ (-(2 : ℝ)) +
          (b - a) * lam₃ ^ 2 * lam₂ ^ (-(3 : ℝ)) =
        (b - a) * (lam₄ * lam₂ ^ (-(2 : ℝ)) +
          lam₃ ^ 2 * lam₂ ^ (-(3 : ℝ))) := by ring
      _ = (b - a) * d / F := by
        rw [hlam₂, hlam₃, hlam₄, fourth_scale hc₁ hF hN,
          third_scale hc₁ hF hN, hd, Real.rpow_neg_one]
        ring
  have hR₂0 : 0 ≤ gkR₂ lam₂ lam₃ lam₄ a b := by
    unfold gkR₂
    have : 0 ≤ b - a := sub_nonneg.mpr hab
    positivity
  have hR₂N : gkR₂ lam₂ lam₃ lam₄ a b ≤ N * d / F := by
    rw [hR₂eq]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hbaN hd0.le) hF.le

  change ‖S - Main‖ ≤ C * (L + T)
  by_cases hFlarge : 1 ≤ F
  · have hconstR₂ : c₂ * d ≤ (d * c₂ / Real.log 2) * L := by
      calc
        c₂ * d = d * c₂ * 1 := by ring
        _ ≤ d * c₂ * (L / Real.log 2) :=
          mul_le_mul_of_nonneg_left honeL (mul_nonneg hd0.le hc₂.le)
        _ = (d * c₂ / Real.log 2) * L := by ring
    have hcardR₂ : (J.card : ℝ) * gkR₂ lam₂ lam₃ lam₄ a b ≤
        d * T + (d * c₂ / Real.log 2) * L := by
      calc
        (J.card : ℝ) * gkR₂ lam₂ lam₃ lam₄ a b ≤
            (c₂ * y + 1) * gkR₂ lam₂ lam₃ lam₄ a b :=
          mul_le_mul_of_nonneg_right hcard hR₂0
        _ ≤ (c₂ * y + 1) * (N * d / F) :=
          mul_le_mul_of_nonneg_left hR₂N (by positivity)
        _ = c₂ * d + d * (N / F) := by
          rw [hy]
          field_simp [hF.ne', hN.ne']
        _ ≤ c₂ * d + d * T := by
          have hNF : N / F ≤ T := by
            rw [hT]
            exact div_le_inverse_sqrt_mul hFlarge hN.le
          exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hNF hd0.le)
        _ ≤ (d * c₂ / Real.log 2) * L + d * T := add_le_add hconstR₂ le_rfl
        _ = d * T + (d * c₂ / Real.log 2) * L := by ring
    have hraw' := hraw a b lam₂ lam₃ lam₄ f xν (by linarith) hab
      hlam₂0 hlam₃0 hlam₄0 hf
      (fun z hz => by rw [hlam₂]; linarith [(h₂ z hz).1])
      (fun z hz => by simpa [hlam₃] using h₃ z hz)
      (fun z hz => by simpa [hlam₄] using h₄ z hz)
      hxν
    change ‖S - Main‖ ≤ K₃₅ * Real.log H + 4 * K₃₂ * s +
      K₃₄ * ((∑ ν ∈ J, gkR₁ lam₂ a b (xν ν)) +
        (J.card : ℝ) * gkR₂ lam₂ lam₃ lam₄ a b) at hraw'
    calc
      ‖S - Main‖ ≤ K₃₅ * Real.log H + 4 * K₃₂ * s +
          K₃₄ * ((∑ ν ∈ J, gkR₁ lam₂ a b (xν ν)) +
            (J.card : ℝ) * gkR₂ lam₂ lam₃ lam₄ a b) := hraw'
      _ ≤ K₃₅ * (Klog * L) + 4 * K₃₂ * (r * T) +
          K₃₄ * ((2 * r * T + (2 * q * Kharm) * L) +
            (d * T + (d * c₂ / Real.log 2) * L)) := by
        exact add_le_add (add_le_add
          (mul_le_mul_of_nonneg_left hlogH hK₃₅)
          (mul_le_mul_of_nonneg_left hsScale.le (by positivity)))
          (mul_le_mul_of_nonneg_left (add_le_add hR₁ hcardR₂) hK₃₄)
      _ = Alog * L + Atime * T := by rw [hAlog, hAtime]; ring
      _ ≤ Clarge * (L + T) := by
        calc
          Alog * L + Atime * T ≤
              Alog * (L + T) + Atime * (L + T) :=
            add_le_add
              (mul_le_mul_of_nonneg_left
                (le_add_of_nonneg_right hT0.le) hAlog0)
              (mul_le_mul_of_nonneg_left
                (le_add_of_nonneg_left hL0) hAtime0)
          _ = Clarge * (L + T) := by rw [hClarge]; ring
      _ ≤ C * (L + T) := by
        apply mul_le_mul_of_nonneg_right _ (add_nonneg hL0 hT0.le)
        rw [hC]
        exact le_add_of_nonneg_right hCsmall0
  · have hFsmall : F < 1 := lt_of_not_ge hFlarge
    have hFhalf : F ^ ((1 : ℝ) / 2) ≤ 1 :=
      Real.rpow_le_one hF.le hFsmall.le (by norm_num)
    have honeFinv : 1 ≤ F ^ (-(1 : ℝ) / 2) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hF hFsmall.le (by norm_num)
    have hNleT : N ≤ T := by
      rw [hT]
      calc
        N = 1 * N := by ring
        _ ≤ F ^ (-(1 : ℝ) / 2) * N :=
          mul_le_mul_of_nonneg_right honeFinv hN.le
    have hFmul : F * F ^ (-(1 : ℝ) / 2) = F ^ ((1 : ℝ) / 2) := by
      calc
        F * F ^ (-(1 : ℝ) / 2) = F ^ (1 : ℝ) * F ^ (-(1 : ℝ) / 2) := by
          rw [Real.rpow_one]
        _ = F ^ ((1 : ℝ) + (-(1 : ℝ) / 2)) := by rw [← Real.rpow_add hF]
        _ = F ^ ((1 : ℝ) / 2) := by ring_nf
    have hyT : y * T = F ^ ((1 : ℝ) / 2) := by
      rw [hy, hT]
      calc
        (F * N⁻¹) * (F ^ (-(1 : ℝ) / 2) * N) =
            (F * F ^ (-(1 : ℝ) / 2)) * (N⁻¹ * N) := by ring
        _ = F ^ ((1 : ℝ) / 2) * 1 := by rw [hFmul, inv_mul_cancel₀ hN.ne']
        _ = F ^ ((1 : ℝ) / 2) := by ring
    have hS3N : ‖S‖ ≤ 3 * N := by
      rw [hS]
      calc
        ‖∑ n ∈ intRange a b, e (f n)‖ ≤
            ∑ n ∈ intRange a b, ‖e (f n)‖ := norm_sum_le _ _
        _ = (intRange a b).card := by simp [norm_e]
        _ ≤ 3 * N := card_intRange_le hN hNa hab hb2N
    have hterm (ν : ℤ) (hν : ν ∈ J) :
        ‖e (f (xν ν) - (ν : ℝ) * xν ν - 1 / 8) /
          ((Real.sqrt |iteratedDeriv 2 f (xν ν)| : ℝ) : ℂ)‖ ≤ s := by
      obtain ⟨hxroot, _⟩ := hxJ ν hν
      have hlo : lam₂ ≤ -iteratedDeriv 2 f (xν ν) := by
        rw [hlam₂]
        exact (h₂ (xν ν) hxroot).1
      have hneg : iteratedDeriv 2 f (xν ν) < 0 := by linarith
      have habs : lam₂ ≤ |iteratedDeriv 2 f (xν ν)| := by
        simpa only [abs_of_neg hneg] using hlo
      have habs0 : 0 < |iteratedDeriv 2 f (xν ν)| := hlam₂0.trans_le habs
      have hsqrt : s = 1 / Real.sqrt lam₂ := by
        rw [hs]
        exact (GK34.rpow_half_facts hlam₂0).2.2
      rw [norm_div, PS.norm_e_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.sqrt_pos.2 habs0), hsqrt]
      exact one_div_le_one_div_of_le (Real.sqrt_pos.2 hlam₂0) (Real.sqrt_le_sqrt habs)
    have hMainCard : ‖Main‖ ≤ (J.card : ℝ) * s := by
      rw [hMain]
      calc
        ‖∑ ν ∈ J, e (f (xν ν) - (ν : ℝ) * xν ν - 1 / 8) /
            ((Real.sqrt |iteratedDeriv 2 f (xν ν)| : ℝ) : ℂ)‖ ≤
          ∑ ν ∈ J, ‖e (f (xν ν) - (ν : ℝ) * xν ν - 1 / 8) /
            ((Real.sqrt |iteratedDeriv 2 f (xν ν)| : ℝ) : ℂ)‖ := norm_sum_le _ _
        _ ≤ ∑ _ν ∈ J, s := Finset.sum_le_sum (fun ν hν => hterm ν hν)
        _ = (J.card : ℝ) * s := by rw [Finset.sum_const, nsmul_eq_mul]
    have hMainBound : ‖Main‖ ≤ r * c₂ + r * T := by
      calc
        ‖Main‖ ≤ (J.card : ℝ) * s := hMainCard
        _ ≤ (c₂ * y + 1) * s := mul_le_mul_of_nonneg_right hcard hs0.le
        _ = r * (c₂ * (y * T) + T) := by rw [hsScale]; ring
        _ = r * (c₂ * F ^ ((1 : ℝ) / 2) + T) := by rw [hyT]
        _ ≤ r * (c₂ + T) := by
          apply mul_le_mul_of_nonneg_left _ hr0.le
          have hc₂half : c₂ * F ^ ((1 : ℝ) / 2) ≤ c₂ := by
            simpa only [mul_one] using
              (mul_le_mul_of_nonneg_left hFhalf hc₂.le)
          exact add_le_add hc₂half le_rfl
        _ = r * c₂ + r * T := by ring
    have hconstSmall : r * c₂ ≤ (c₂ * r / Real.log 2) * L := by
      calc
        r * c₂ = c₂ * r * 1 := by ring
        _ ≤ c₂ * r * (L / Real.log 2) :=
          mul_le_mul_of_nonneg_left honeL (mul_nonneg hc₂.le hr0.le)
        _ = (c₂ * r / Real.log 2) * L := by ring
    calc
      ‖S - Main‖ ≤ ‖S‖ + ‖Main‖ := norm_sub_le _ _
      _ ≤ 3 * N + (r * c₂ + r * T) := add_le_add hS3N hMainBound
      _ ≤ r * c₂ + (3 + r) * T := by
        have h3N : 3 * N ≤ 3 * T :=
          mul_le_mul_of_nonneg_left hNleT (by norm_num)
        calc
          3 * N + (r * c₂ + r * T) = r * c₂ + (3 * N + r * T) := by ring
          _ ≤ r * c₂ + (3 * T + r * T) :=
            add_le_add le_rfl (add_le_add h3N le_rfl)
          _ = r * c₂ + (3 + r) * T := by ring
      _ ≤ (c₂ * r / Real.log 2) * L + (3 + r) * T :=
        add_le_add hconstSmall le_rfl
      _ ≤ Csmall * (L + T) := by
        have hsmallLog : 0 ≤ c₂ * r / Real.log 2 :=
          div_nonneg (mul_nonneg hc₂.le hr0.le) hlog2.le
        have hsmallTime : 0 ≤ 3 + r := by positivity
        calc
          (c₂ * r / Real.log 2) * L + (3 + r) * T ≤
              (c₂ * r / Real.log 2) * (L + T) +
                (3 + r) * (L + T) :=
            add_le_add
              (mul_le_mul_of_nonneg_left
                (le_add_of_nonneg_right hT0.le) hsmallLog)
              (mul_le_mul_of_nonneg_left
                (le_add_of_nonneg_left hL0) hsmallTime)
          _ = Csmall * (L + T) := by rw [hCsmall]; ring
      _ ≤ C * (L + T) := by
        apply mul_le_mul_of_nonneg_right _ (add_nonneg hL0 hT0.le)
        rw [hC]
        exact le_add_of_nonneg_left hClarge0

end LeanProofs.IntegerPoints
