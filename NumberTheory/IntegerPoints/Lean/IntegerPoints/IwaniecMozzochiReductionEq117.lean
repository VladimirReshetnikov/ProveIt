import IntegerPoints.IwaniecMozzochi
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Iwaniec--Mozzochi (11.7) from Lemma 11.1

This file isolates the elementary last step of Section 11.  Conditional on
the two analytic assertions in Lemma 11.1, the pointwise bounds (11.6) and
the support condition `x \asymp X` give the claimed `X⁻²` remainder in
(11.7).

The only support detail which is not literally visible in the statement of
(11.7) is that derivatives of a smooth compactly supported function have no
larger topological support.  We make that step explicit below and then bound
the two `L²` norms on the interval `(0, X / c₀]`.
-/

open Real Set MeasureTheory

namespace LeanProofs.IntegerPoints

/-- Every iterated one-dimensional derivative is topologically supported
inside the topological support of the original function. -/
private theorem eq117_tsupport_iteratedDeriv_subset (f : ℝ → ℝ) (n : ℕ) :
    tsupport (iteratedDeriv n f) ⊆ tsupport f := by
  induction n with
  | zero => simp
  | succ n ih =>
      simpa only [Nat.succ_eq_add_one, iteratedDeriv_succ] using
        (tsupport_deriv_subset (f := iteratedDeriv n f)).trans ih

/-- If `f` is supported in `[lo, hi]`, then the square of every iterated
derivative is supported in `(0, hi]`; a global pointwise bound `B` therefore
bounds its squared integral by `B² hi`. -/
private theorem eq117_integral_iteratedDeriv_sq_le
    (f : ℝ → ℝ) (n : ℕ) {lo hi B : ℝ}
    (hlo : 0 < lo) (hhi : 0 < hi)
    (hsupp : ∀ t : ℝ, f t ≠ 0 → lo ≤ t ∧ t ≤ hi)
    (hbound : ∀ t : ℝ, |iteratedDeriv n f t| ≤ B) :
    (∫ t : ℝ, iteratedDeriv n f t ^ 2) ≤ B ^ 2 * hi := by
  have htsupport : tsupport f ⊆ Icc lo hi :=
    closure_minimal (fun t ht => hsupp t ht) isClosed_Icc
  have hderivSupport : Function.support (iteratedDeriv n f) ⊆ Ioc (0 : ℝ) hi := by
    intro t ht
    have htDeriv : t ∈ tsupport (iteratedDeriv n f) := subset_closure ht
    have htF : t ∈ tsupport f := eq117_tsupport_iteratedDeriv_subset f n htDeriv
    have htIcc := htsupport htF
    exact ⟨hlo.trans_le htIcc.1, htIcc.2⟩
  have hsquareSupport :
      Function.support (fun t : ℝ => iteratedDeriv n f t ^ 2) ⊆ Ioc (0 : ℝ) hi := by
    intro t ht
    apply hderivSupport
    intro hz
    apply ht
    simp [hz]
  have hintegral :
      (∫ t in (0 : ℝ)..hi, iteratedDeriv n f t ^ 2) =
        ∫ t : ℝ, iteratedDeriv n f t ^ 2 :=
    intervalIntegral.integral_eq_integral_of_support_subset hsquareSupport
  have hnorm :
      ‖∫ t in (0 : ℝ)..hi, iteratedDeriv n f t ^ 2‖ ≤
        B ^ 2 * |hi - 0| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun t _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hbound t) 2
  rw [hintegral] at hnorm
  calc
    (∫ t : ℝ, iteratedDeriv n f t ^ 2) ≤
        ‖∫ t : ℝ, iteratedDeriv n f t ^ 2‖ := by
      rw [Real.norm_eq_abs]
      exact le_abs_self _
    _ ≤ B ^ 2 * |hi - 0| := hnorm
    _ = B ^ 2 * hi := by rw [sub_zero, abs_of_pos hhi]

private theorem eq117_second_deriv_scale {c₀ c₁ X : ℝ} (hX : 0 < X) :
    (c₁ * X ^ (-(2 : ℝ))) ^ 2 * (X / c₀) =
      (c₁ ^ 2 / c₀) * X ^ (-(3 : ℝ)) := by
  have hpow : (X ^ (-(2 : ℝ))) ^ 2 = X ^ (-(4 : ℝ)) := by
    calc
      (X ^ (-(2 : ℝ))) ^ 2 = X ^ ((-(2 : ℝ)) * (2 : ℕ)) :=
        (Real.rpow_mul_natCast hX.le (-(2 : ℝ)) 2).symm
      _ = X ^ (-(4 : ℝ)) := by norm_num
  have hcombine : X ^ (-(4 : ℝ)) * X = X ^ (-(3 : ℝ)) := by
    calc
      X ^ (-(4 : ℝ)) * X = X ^ (-(4 : ℝ) + 1) :=
        (Real.rpow_add_one hX.ne' (-(4 : ℝ))).symm
      _ = X ^ (-(3 : ℝ)) := by norm_num
  rw [mul_pow, hpow]
  calc
    c₁ ^ 2 * X ^ (-(4 : ℝ)) * (X / c₀) =
        (c₁ ^ 2 / c₀) * (X ^ (-(4 : ℝ)) * X) := by ring
    _ = (c₁ ^ 2 / c₀) * X ^ (-(3 : ℝ)) := by rw [hcombine]

private theorem eq117_third_deriv_scale {c₀ c₁ X : ℝ} (hX : 0 < X) :
    (c₁ * X ^ (-(3 : ℝ))) ^ 2 * (X / c₀) =
      (c₁ ^ 2 / c₀) * X ^ (-(5 : ℝ)) := by
  have hpow : (X ^ (-(3 : ℝ))) ^ 2 = X ^ (-(6 : ℝ)) := by
    calc
      (X ^ (-(3 : ℝ))) ^ 2 = X ^ ((-(3 : ℝ)) * (2 : ℕ)) :=
        (Real.rpow_mul_natCast hX.le (-(3 : ℝ)) 2).symm
      _ = X ^ (-(6 : ℝ)) := by norm_num
  have hcombine : X ^ (-(6 : ℝ)) * X = X ^ (-(5 : ℝ)) := by
    calc
      X ^ (-(6 : ℝ)) * X = X ^ (-(6 : ℝ) + 1) :=
        (Real.rpow_add_one hX.ne' (-(6 : ℝ))).symm
      _ = X ^ (-(5 : ℝ)) := by norm_num
  rw [mul_pow, hpow]
  calc
    c₁ ^ 2 * X ^ (-(6 : ℝ)) * (X / c₀) =
        (c₁ ^ 2 / c₀) * (X ^ (-(6 : ℝ)) * X) := by ring
    _ = (c₁ ^ 2 / c₀) * X ^ (-(5 : ℝ)) := by rw [hcombine]

/-- The fourth-root product dictated by (11.4) has exactly scale `X⁻²`. -/
private theorem eq117_quarter_scale_product {D X : ℝ} (hD : 0 < D) (hX : 0 < X) :
    (D * X ^ (-(3 : ℝ))) ^ ((1 : ℝ) / 4) *
        (D * X ^ (-(5 : ℝ))) ^ ((1 : ℝ) / 4) =
      D ^ ((1 : ℝ) / 2) * X ^ (-(2 : ℝ)) := by
  rw [Real.mul_rpow hD.le (Real.rpow_nonneg hX.le _),
    Real.mul_rpow hD.le (Real.rpow_nonneg hX.le _)]
  have hX3 :
      (X ^ (-(3 : ℝ))) ^ ((1 : ℝ) / 4) = X ^ (-(3 : ℝ) / 4) := by
    calc
      (X ^ (-(3 : ℝ))) ^ ((1 : ℝ) / 4) =
          X ^ ((-(3 : ℝ)) * ((1 : ℝ) / 4)) :=
        (Real.rpow_mul hX.le (-(3 : ℝ)) ((1 : ℝ) / 4)).symm
      _ = X ^ (-(3 : ℝ) / 4) := by congr 1 <;> ring
  have hX5 :
      (X ^ (-(5 : ℝ))) ^ ((1 : ℝ) / 4) = X ^ (-(5 : ℝ) / 4) := by
    calc
      (X ^ (-(5 : ℝ))) ^ ((1 : ℝ) / 4) =
          X ^ ((-(5 : ℝ)) * ((1 : ℝ) / 4)) :=
        (Real.rpow_mul hX.le (-(5 : ℝ)) ((1 : ℝ) / 4)).symm
      _ = X ^ (-(5 : ℝ) / 4) := by congr 1 <;> ring
  rw [hX3, hX5]
  calc
    D ^ ((1 : ℝ) / 4) * X ^ (-(3 : ℝ) / 4) *
          (D ^ ((1 : ℝ) / 4) * X ^ (-(5 : ℝ) / 4)) =
        (D ^ ((1 : ℝ) / 4) * D ^ ((1 : ℝ) / 4)) *
          (X ^ (-(3 : ℝ) / 4) * X ^ (-(5 : ℝ) / 4)) := by ring
    _ = D ^ ((1 : ℝ) / 4 + (1 : ℝ) / 4) *
          X ^ (-(3 : ℝ) / 4 + -(5 : ℝ) / 4) := by
      rw [Real.rpow_add hD, Real.rpow_add hX]
    _ = D ^ ((1 : ℝ) / 2) * X ^ (-(2 : ℝ)) := by
      congr 1 <;> ring

private theorem eq117_half_l2_product_le {u v D X : ℝ}
    (hu0 : 0 ≤ u) (hv0 : 0 ≤ v) (hD : 0 < D) (hX : 0 < X)
    (hu : u ≤ D * X ^ (-(3 : ℝ)))
    (hv : v ≤ D * X ^ (-(5 : ℝ))) :
    Real.sqrt u ^ ((1 : ℝ) / 2) * Real.sqrt v ^ ((1 : ℝ) / 2) ≤
      D ^ ((1 : ℝ) / 2) * X ^ (-(2 : ℝ)) := by
  have huRoot :
      Real.sqrt u ^ ((1 : ℝ) / 2) = u ^ ((1 : ℝ) / 4) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hu0]
    congr 1 <;> ring
  have hvRoot :
      Real.sqrt v ^ ((1 : ℝ) / 2) = v ^ ((1 : ℝ) / 4) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hv0]
    congr 1 <;> ring
  rw [huRoot, hvRoot]
  calc
    u ^ ((1 : ℝ) / 4) * v ^ ((1 : ℝ) / 4) ≤
        (D * X ^ (-(3 : ℝ))) ^ ((1 : ℝ) / 4) *
          (D * X ^ (-(5 : ℝ))) ^ ((1 : ℝ) / 4) := by
      exact mul_le_mul
        (Real.rpow_le_rpow hu0 hu (by norm_num))
        (Real.rpow_le_rpow hv0 hv (by norm_num))
        (Real.rpow_nonneg hv0 _)
        (Real.rpow_nonneg (mul_nonneg hD.le (Real.rpow_nonneg hX.le _)) _)
    _ = D ^ ((1 : ℝ) / 2) * X ^ (-(2 : ℝ)) :=
      eq117_quarter_scale_product hD hX

/-- **Iwaniec--Mozzochi (11.7), conditionally on Lemma 11.1.** -/
theorem iwaniecMozzochi_eq117_of_lemma111
    (h112113 : iwaniecMozzochi_lemma111_eq112_eq113)
    (h114 : iwaniecMozzochi_lemma111_eq114) :
    iwaniecMozzochi_eq117 := by
  rcases h112113 with ⟨C₁₁₁, hC₁₁₁⟩
  intro c₀ c₁ hc₀ _hc₀_one hc₁
  let D : ℝ := c₁ ^ 2 / c₀
  have hD : 0 < D := by
    dsimp [D]
    exact div_pos (pow_pos hc₁ 2) hc₀
  refine ⟨|C₁₁₁| * Real.sqrt (2 * π) * D ^ ((1 : ℝ) / 2), ?_⟩
  intro f a b X hf ha hb hX hsupp hderiv2 hderiv3
  have hlo : 0 < c₀ * X := mul_pos hc₀ hX
  have hhi : 0 < X / c₀ := div_pos hX hc₀
  let u : ℝ := ∫ t : ℝ, iteratedDeriv 2 f t ^ 2
  let v : ℝ := ∫ t : ℝ, iteratedDeriv 3 f t ^ 2
  have hu0 : 0 ≤ u := by
    dsimp [u]
    exact integral_nonneg fun t => sq_nonneg (iteratedDeriv 2 f t)
  have hv0 : 0 ≤ v := by
    dsimp [v]
    exact integral_nonneg fun t => sq_nonneg (iteratedDeriv 3 f t)
  have hu : u ≤ D * X ^ (-(3 : ℝ)) := by
    have h := eq117_integral_iteratedDeriv_sq_le f 2 hlo hhi hsupp hderiv2
    rw [eq117_second_deriv_scale hX] at h
    simpa only [u, D] using h
  have hv : v ≤ D * X ^ (-(5 : ℝ)) := by
    have h := eq117_integral_iteratedDeriv_sq_le f 3 hlo hhi hsupp hderiv3
    rw [eq117_third_deriv_scale hX] at h
    simpa only [v, D] using h
  have hL2 :
      imL2Norm (iteratedDeriv 2 f) ^ ((1 : ℝ) / 2) *
          imL2Norm (iteratedDeriv 3 f) ^ ((1 : ℝ) / 2) ≤
        D ^ ((1 : ℝ) / 2) * X ^ (-(2 : ℝ)) := by
    unfold imL2Norm
    exact eq117_half_l2_product_le hu0 hv0 hD hX hu hv
  have hmoment :
      secondMomentFourier f ≤
        (Real.sqrt (2 * π) * D ^ ((1 : ℝ) / 2)) * X ^ (-(2 : ℝ)) := by
    calc
      secondMomentFourier f ≤
          Real.sqrt (2 * π) * imL2Norm (iteratedDeriv 2 f) ^ ((1 : ℝ) / 2) *
            imL2Norm (iteratedDeriv 3 f) ^ ((1 : ℝ) / 2) := h114 f hf
      _ ≤ Real.sqrt (2 * π) *
          (D ^ ((1 : ℝ) / 2) * X ^ (-(2 : ℝ))) := by
        have hsqrt : 0 ≤ Real.sqrt (2 * π) := Real.sqrt_nonneg _
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hL2 hsqrt
      _ = (Real.sqrt (2 * π) * D ^ ((1 : ℝ) / 2)) * X ^ (-(2 : ℝ)) := by ring
  let P : ℝ :=
    b ^ (-(3 : ℝ) / 2) + a ^ (-(1 : ℝ) / 2) * b ^ (-(2 : ℝ))
  have hP : 0 ≤ P := by
    dsimp [P]
    exact add_nonneg (Real.rpow_nonneg hb.le _)
      (mul_nonneg (Real.rpow_nonneg ha.le _) (Real.rpow_nonneg hb.le _))
  have hmoment0 : 0 ≤ secondMomentFourier f := by
    unfold secondMomentFourier
    exact integral_nonneg fun y => mul_nonneg (sq_nonneg y) (norm_nonneg _)
  have hbase := hC₁₁₁ f a b hf ha hb
  have habsC : C₁₁₁ * (P * secondMomentFourier f) ≤
      |C₁₁₁| * (P * secondMomentFourier f) :=
    mul_le_mul_of_nonneg_right (le_abs_self C₁₁₁) (mul_nonneg hP hmoment0)
  calc
    ‖incompleteBessel f a b -
        (2 * Complex.I * (a : ℂ)) ^ (-(1 : ℂ) / 2) *
          e (-2 * Real.sqrt (a * b)) * (f (Real.sqrt (a / b)) : ℂ)‖ ≤
        C₁₁₁ * (P * secondMomentFourier f) := by
      simpa only [P] using hbase
    _ ≤ |C₁₁₁| * (P * secondMomentFourier f) := habsC
    _ ≤ |C₁₁₁| *
        (P * ((Real.sqrt (2 * π) * D ^ ((1 : ℝ) / 2)) * X ^ (-(2 : ℝ)))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hmoment hP) (abs_nonneg C₁₁₁)
    _ = (|C₁₁₁| * Real.sqrt (2 * π) * D ^ ((1 : ℝ) / 2)) *
        (P * X ^ (-(2 : ℝ))) := by ring
    _ = (|C₁₁₁| * Real.sqrt (2 * π) * D ^ ((1 : ℝ) / 2)) *
        ((b ^ (-(3 : ℝ) / 2) + a ^ (-(1 : ℝ) / 2) * b ^ (-(2 : ℝ))) *
          X ^ (-(2 : ℝ))) := by simp only [P]

end LeanProofs.IntegerPoints
