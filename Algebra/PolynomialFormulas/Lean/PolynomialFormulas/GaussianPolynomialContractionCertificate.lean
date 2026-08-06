import PolynomialFormulas.GaussianPolynomialApproximationCore
import PolynomialFormulas.GaussianPolynomialContraction

/-!
# Executable contraction certificates for Gaussian-rational quartics

This file turns the analytic Banach argument in
`GaussianPolynomialContraction` into a certificate whose data and tests are
entirely rational.

For a polynomial `p`, a Gaussian-rational center `c`, and a rational radius
`r`, let `a₀, ..., a₄` be the coefficients of `p(c + X)`.  When `a₁ != 0`, put
`bᵢ = aᵢ / a₁`.  The frozen Newton map has the form

`c - b₀ - b₂ (z-c)² - b₃ (z-c)³ - b₄ (z-c)⁴`.

On the radius-`r` disk its Lipschitz constant is bounded by the exact rational
number

`L = 2 |b₂|₁ r + 3 |b₃|₁ r² + 4 |b₄|₁ r³`.

Thus the decidable inequalities `L < 1` and `|b₀|₁ + L*r <= r` certify a
genuine complex root in that disk.  The derived radius `2 * |b₀|₁` reduces the
second inequality to the single test `2*L <= 1`.
-/

namespace LeanProofs.PolynomialFormulas

namespace GaussianPolynomialContractionCertificate

open GaussianPolynomialApproximationCore
open GaussianPolynomialApproximationCore.QPoly
open GaussianPolynomialContraction
open Metric
open scoped NNReal

/-! ## Executable rational data -/

/-- The `i`th coefficient of `p(c + X)`. -/
def shiftedCoeff (p : QPoly4) (c : GaussianRat) (i : Fin 5) : GaussianRat :=
  (translate c p) i

/-- The linear coefficient of `p(c + X)`.  This is `p'(c)`. -/
def linearCoeff (p : QPoly4) (c : GaussianRat) : GaussianRat :=
  shiftedCoeff p c 1

/-- The normalized shifted coefficient `aᵢ / a₁`. -/
def normalizedCoeff (p : QPoly4) (c : GaussianRat) (i : Fin 5) : GaussianRat :=
  shiftedCoeff p c i / linearCoeff p c

/-- Rational upper bound for the displacement of the center under the frozen
Newton map. -/
def displacementL1 (p : QPoly4) (c : GaussianRat) : ℚ :=
  GaussianRat.l1 (normalizedCoeff p c 0)

/-- Rational Lipschitz bound for the frozen Newton map on the radius-`r`
closed disk. -/
def contractionL1 (p : QPoly4) (c : GaussianRat) (r : ℚ) : ℚ :=
  2 * GaussianRat.l1 (normalizedCoeff p c 2) * r +
  3 * GaussianRat.l1 (normalizedCoeff p c 3) * r ^ 2 +
  4 * GaussianRat.l1 (normalizedCoeff p c 4) * r ^ 3

/-- All rational conditions needed by the contraction proof. -/
def IsValid (p : QPoly4) (c : GaussianRat) (r : ℚ) : Prop :=
  0 ≤ r ∧
  linearCoeff p c ≠ 0 ∧
  contractionL1 p c r < 1 ∧
  displacementL1 p c + contractionL1 p c r * r ≤ r

/-- Executable decision procedure for a supplied center and radius. -/
def valid (p : QPoly4) (c : GaussianRat) (r : ℚ) : Bool :=
  decide
    (0 ≤ r ∧
      linearCoeff p c ≠ 0 ∧
      contractionL1 p c r < 1 ∧
      displacementL1 p c + contractionL1 p c r * r ≤ r)

@[simp]
theorem valid_eq_true (p : QPoly4) (c : GaussianRat) (r : ℚ) :
    valid p c r = true ↔ IsValid p c r := by
  simp [valid, IsValid]

/-- The canonical radius associated with a center. -/
def newtonRadius (p : QPoly4) (c : GaussianRat) : ℚ :=
  2 * displacementL1 p c

/-- A radius-free certificate.  Its radius is computed by `newtonRadius`. -/
def AutoValid (p : QPoly4) (c : GaussianRat) : Prop :=
  linearCoeff p c ≠ 0 ∧
  2 * contractionL1 p c (newtonRadius p c) ≤ 1

/-- Executable decision procedure for the radius-free certificate. -/
def autoValid (p : QPoly4) (c : GaussianRat) : Bool :=
  decide
    (linearCoeff p c ≠ 0 ∧
      2 * contractionL1 p c (newtonRadius p c) ≤ 1)

@[simp]
theorem autoValid_eq_true (p : QPoly4) (c : GaussianRat) :
    autoValid p c = true ↔ AutoValid p c := by
  simp [autoValid, AutoValid]

theorem displacementL1_nonneg (p : QPoly4) (c : GaussianRat) :
    0 <= displacementL1 p c :=
  GaussianRat.l1_nonneg _

theorem contractionL1_nonneg (p : QPoly4) (c : GaussianRat) {r : ℚ}
    (hr : 0 <= r) : 0 <= contractionL1 p c r := by
  unfold contractionL1
  have h2 := GaussianRat.l1_nonneg (normalizedCoeff p c 2)
  have h3 := GaussianRat.l1_nonneg (normalizedCoeff p c 3)
  have h4 := GaussianRat.l1_nonneg (normalizedCoeff p c 4)
  positivity

theorem newtonRadius_nonneg (p : QPoly4) (c : GaussianRat) :
    0 <= newtonRadius p c := by
  unfold newtonRadius
  positivity [displacementL1_nonneg p c]

private theorem selfMap_of_two_mul_le_one (s L : ℚ) (hs : 0 ≤ s)
    (hL : 2 * L ≤ 1) : s + L * (2 * s) ≤ 2 * s := by
  calc
    s + L * (2 * s) = s + (2 * L) * s := by ring
    _ ≤ s + 1 * s :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right hL hs)
    _ = 2 * s := by ring

/-- The radius-free test implies all conditions of the raw certificate. -/
theorem autoValid_isValid {p : QPoly4} {c : GaussianRat}
    (h : AutoValid p c) : IsValid p c (newtonRadius p c) := by
  unfold AutoValid at h
  unfold IsValid
  unfold newtonRadius at h ⊢
  rcases h with ⟨hlinear, hcontract⟩
  have hs : 0 ≤ displacementL1 p c := displacementL1_nonneg p c
  have hr : 0 ≤ 2 * displacementL1 p c := mul_nonneg (by norm_num) hs
  have hLlt :
      contractionL1 p c (2 * displacementL1 p c) < 1 := by
    linarith
  exact ⟨hr, hlinear, hLlt,
    selfMap_of_two_mul_le_one _ _ hs hcontract⟩

/-! ## Analytic estimates -/

/-- Difference-of-powers estimate on a closed disk. -/
theorem norm_pow_sub_pow_le (x y : ℂ) (r : ℝ) (hr : 0 <= r)
    (hx : ‖x‖ <= r) (hy : ‖y‖ <= r) (n : ℕ) :
    ‖x ^ n - y ^ n‖ <= (n : ℝ) * r ^ (n - 1) * ‖x - y‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ]
      rw [show x ^ n * x - y ^ n * y =
          x ^ n * (x - y) + (x ^ n - y ^ n) * y by ring]
      calc
        ‖x ^ n * (x - y) + (x ^ n - y ^ n) * y‖
            <= ‖x ^ n * (x - y)‖ + ‖(x ^ n - y ^ n) * y‖ :=
          norm_add_le _ _
        _ <= ‖x ^ n‖ * ‖x - y‖ + ‖x ^ n - y ^ n‖ * ‖y‖ :=
          add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
        _ <= (‖x‖ ^ n) * ‖x - y‖ + ‖x ^ n - y ^ n‖ * ‖y‖ :=
          add_le_add
            (mul_le_mul_of_nonneg_right (norm_pow_le x n) (norm_nonneg _)) le_rfl
        _ <= r ^ n * ‖x - y‖ +
            ((n : ℝ) * r ^ (n - 1) * ‖x - y‖) * r := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_right
              (pow_le_pow_left₀ (norm_nonneg x) hx n) (norm_nonneg _)
          · exact mul_le_mul ih hy (norm_nonneg _) (by positivity)
        _ = ((n + 1 : ℕ) : ℝ) * r ^ ((n + 1 : ℕ) - 1) * ‖x - y‖ := by
          cases n with
          | zero => simp
          | succ n =>
              simp only [Nat.cast_add, Nat.cast_one, Nat.succ_sub_one]
              rw [pow_succ]
              ring

/-- Evaluation after shifting to `c`, written out in degree four. -/
theorem evalComplex_eq_shiftedExpansion (p : QPoly4) (c : GaussianRat) (z : ℂ) :
    evalComplex p z =
      GaussianRat.toComplex (shiftedCoeff p c 0) +
        (GaussianRat.toComplex (shiftedCoeff p c 1) *
            (z - GaussianRat.toComplex c) +
          (GaussianRat.toComplex (shiftedCoeff p c 2) *
              (z - GaussianRat.toComplex c) ^ 2 +
            (GaussianRat.toComplex (shiftedCoeff p c 3) *
                (z - GaussianRat.toComplex c) ^ 3 +
              GaussianRat.toComplex (shiftedCoeff p c 4) *
                (z - GaussianRat.toComplex c) ^ 4))) := by
  calc
    evalComplex p z =
        evalComplex p ((z - GaussianRat.toComplex c) + GaussianRat.toComplex c) := by
      congr 1
      ring
    _ = evalComplex (translate c p) (z - GaussianRat.toComplex c) := by
      rw [evalComplex_translate]
    _ = ∑ i : Fin 5,
        GaussianRat.toComplex ((translate c p) i) *
          (z - GaussianRat.toComplex c) ^ (i : ℕ) :=
      evalComplex_eq_sum _ _
    _ = _ := by
      simp [Fin.sum_univ_succ, shiftedCoeff]

/-- The frozen Newton map written in normalized shifted coefficients. -/
theorem newtonMap_eq_normalized (p : QPoly4) (c : GaussianRat)
    (hlinear : linearCoeff p c ≠ 0) (z : ℂ) :
    newtonMap (toComplexPolynomial p)
        (GaussianRat.toComplex (linearCoeff p c)) z =
      GaussianRat.toComplex c -
        GaussianRat.toComplex (normalizedCoeff p c 0) -
        GaussianRat.toComplex (normalizedCoeff p c 2) *
          (z - GaussianRat.toComplex c) ^ 2 -
        GaussianRat.toComplex (normalizedCoeff p c 3) *
          (z - GaussianRat.toComplex c) ^ 3 -
        GaussianRat.toComplex (normalizedCoeff p c 4) *
          (z - GaussianRat.toComplex c) ^ 4 := by
  rw [newtonMap]
  rw [← evalComplex_eq_toComplexPolynomial_eval]
  rw [evalComplex_eq_shiftedExpansion p c z]
  simp only [normalizedCoeff, GaussianRat.toComplex_div]
  unfold linearCoeff at hlinear ⊢
  field_simp [GaussianRat.toComplex_ne_zero_of_ne_zero hlinear]
  ring

theorem eval_center_div_linear (p : QPoly4) (c : GaussianRat) :
    (toComplexPolynomial p).eval (GaussianRat.toComplex c) /
        GaussianRat.toComplex (linearCoeff p c) =
      GaussianRat.toComplex (normalizedCoeff p c 0) := by
  rw [← evalComplex_eq_toComplexPolynomial_eval]
  rw [evalComplex_eq_shiftedExpansion p c (GaussianRat.toComplex c)]
  simp [normalizedCoeff]

/-! ## Correctness of the executable certificates -/

/-- A valid rational certificate yields a genuine root in the claimed complex
closed disk. -/
theorem isValid_exists_zero_in_closedBall {p : QPoly4} {c : GaussianRat} {r : ℚ}
    (h : IsValid p c r) :
    ∃ z ∈ closedBall (GaussianRat.toComplex c) (r : ℝ), evalComplex p z = 0 := by
  rcases h with ⟨hr, hlinear, hcontract, hstep⟩
  have hrR : 0 <= (r : ℝ) := by exact_mod_cast hr
  have hfactorNonneg : 0 <= contractionL1 p c r :=
    contractionL1_nonneg p c hr
  let K : ℝ≥0 :=
    ⟨(contractionL1 p c r : ℝ), by exact_mod_cast hfactorNonneg⟩
  have hKcoe : (K : ℝ) = (contractionL1 p c r : ℝ) := rfl
  have hK : K < 1 := by
    change (contractionL1 p c r : ℝ) < 1
    exact_mod_cast hcontract
  have hA : GaussianRat.toComplex (linearCoeff p c) ≠ 0 :=
    GaussianRat.toComplex_ne_zero_of_ne_zero hlinear
  have hLip : ∀ z ∈ closedBall (GaussianRat.toComplex c) (r : ℝ),
      ∀ w ∈ closedBall (GaussianRat.toComplex c) (r : ℝ),
        dist
            (newtonMap (toComplexPolynomial p)
              (GaussianRat.toComplex (linearCoeff p c)) z)
            (newtonMap (toComplexPolynomial p)
              (GaussianRat.toComplex (linearCoeff p c)) w) <=
          (K : ℝ) * dist z w := by
    intro z hz w hw
    have hzNorm : ‖z - GaussianRat.toComplex c‖ <= (r : ℝ) := by
      simpa [dist_eq_norm] using (mem_closedBall.mp hz)
    have hwNorm : ‖w - GaussianRat.toComplex c‖ <= (r : ℝ) := by
      simpa [dist_eq_norm] using (mem_closedBall.mp hw)
    have hpow2 := norm_pow_sub_pow_le
      (z - GaussianRat.toComplex c) (w - GaussianRat.toComplex c)
      (r : ℝ) hrR hzNorm hwNorm 2
    have hpow3 := norm_pow_sub_pow_le
      (z - GaussianRat.toComplex c) (w - GaussianRat.toComplex c)
      (r : ℝ) hrR hzNorm hwNorm 3
    have hpow4 := norm_pow_sub_pow_le
      (z - GaussianRat.toComplex c) (w - GaussianRat.toComplex c)
      (r : ℝ) hrR hzNorm hwNorm 4
    norm_num at hpow2 hpow3 hpow4
    have hterm2 :
        ‖GaussianRat.toComplex (normalizedCoeff p c 2) *
            ((z - GaussianRat.toComplex c) ^ 2 -
              (w - GaussianRat.toComplex c) ^ 2)‖ <=
          ((2 * GaussianRat.l1 (normalizedCoeff p c 2) * r : ℚ) : ℝ) *
            ‖z - w‖ := by
      calc
        _ <= ‖GaussianRat.toComplex (normalizedCoeff p c 2)‖ *
              ‖(z - GaussianRat.toComplex c) ^ 2 -
                (w - GaussianRat.toComplex c) ^ 2‖ := norm_mul_le _ _
        _ <= (GaussianRat.l1 (normalizedCoeff p c 2) : ℝ) *
              (2 * (r : ℝ) *
                ‖z - w‖) :=
          mul_le_mul (GaussianRat.norm_toComplex_le_l1 _)
            hpow2 (norm_nonneg _)
              (by exact_mod_cast GaussianRat.l1_nonneg (normalizedCoeff p c 2))
        _ = _ := by
          push_cast
          ring
    have hterm3 :
        ‖GaussianRat.toComplex (normalizedCoeff p c 3) *
            ((z - GaussianRat.toComplex c) ^ 3 -
              (w - GaussianRat.toComplex c) ^ 3)‖ <=
          ((3 * GaussianRat.l1 (normalizedCoeff p c 3) * r ^ 2 : ℚ) : ℝ) *
            ‖z - w‖ := by
      calc
        _ <= ‖GaussianRat.toComplex (normalizedCoeff p c 3)‖ *
              ‖(z - GaussianRat.toComplex c) ^ 3 -
                (w - GaussianRat.toComplex c) ^ 3‖ := norm_mul_le _ _
        _ <= (GaussianRat.l1 (normalizedCoeff p c 3) : ℝ) *
              (3 * (r : ℝ) ^ 2 *
                ‖z - w‖) :=
          mul_le_mul (GaussianRat.norm_toComplex_le_l1 _)
            hpow3 (norm_nonneg _)
              (by exact_mod_cast GaussianRat.l1_nonneg (normalizedCoeff p c 3))
        _ = _ := by
          push_cast
          ring
    have hterm4 :
        ‖GaussianRat.toComplex (normalizedCoeff p c 4) *
            ((z - GaussianRat.toComplex c) ^ 4 -
              (w - GaussianRat.toComplex c) ^ 4)‖ <=
          ((4 * GaussianRat.l1 (normalizedCoeff p c 4) * r ^ 3 : ℚ) : ℝ) *
            ‖z - w‖ := by
      calc
        _ <= ‖GaussianRat.toComplex (normalizedCoeff p c 4)‖ *
              ‖(z - GaussianRat.toComplex c) ^ 4 -
                (w - GaussianRat.toComplex c) ^ 4‖ := norm_mul_le _ _
        _ <= (GaussianRat.l1 (normalizedCoeff p c 4) : ℝ) *
              (4 * (r : ℝ) ^ 3 *
                ‖z - w‖) :=
          mul_le_mul (GaussianRat.norm_toComplex_le_l1 _)
            hpow4 (norm_nonneg _)
              (by exact_mod_cast GaussianRat.l1_nonneg (normalizedCoeff p c 4))
        _ = _ := by
          push_cast
          ring
    rw [newtonMap_eq_normalized p c hlinear z,
      newtonMap_eq_normalized p c hlinear w, dist_eq_norm]
    have hrewrite :
        (GaussianRat.toComplex c -
              GaussianRat.toComplex (normalizedCoeff p c 0) -
              GaussianRat.toComplex (normalizedCoeff p c 2) *
                (z - GaussianRat.toComplex c) ^ 2 -
              GaussianRat.toComplex (normalizedCoeff p c 3) *
                (z - GaussianRat.toComplex c) ^ 3 -
              GaussianRat.toComplex (normalizedCoeff p c 4) *
                (z - GaussianRat.toComplex c) ^ 4) -
            (GaussianRat.toComplex c -
              GaussianRat.toComplex (normalizedCoeff p c 0) -
              GaussianRat.toComplex (normalizedCoeff p c 2) *
                (w - GaussianRat.toComplex c) ^ 2 -
              GaussianRat.toComplex (normalizedCoeff p c 3) *
                (w - GaussianRat.toComplex c) ^ 3 -
              GaussianRat.toComplex (normalizedCoeff p c 4) *
                (w - GaussianRat.toComplex c) ^ 4) =
          -((GaussianRat.toComplex (normalizedCoeff p c 2) *
                ((z - GaussianRat.toComplex c) ^ 2 -
                  (w - GaussianRat.toComplex c) ^ 2) +
              GaussianRat.toComplex (normalizedCoeff p c 3) *
                ((z - GaussianRat.toComplex c) ^ 3 -
                  (w - GaussianRat.toComplex c) ^ 3)) +
            GaussianRat.toComplex (normalizedCoeff p c 4) *
              ((z - GaussianRat.toComplex c) ^ 4 -
                (w - GaussianRat.toComplex c) ^ 4)) := by
      ring
    rw [hrewrite, norm_neg]
    calc
      _ <=
          ‖GaussianRat.toComplex (normalizedCoeff p c 2) *
              ((z - GaussianRat.toComplex c) ^ 2 -
                (w - GaussianRat.toComplex c) ^ 2)‖ +
          ‖GaussianRat.toComplex (normalizedCoeff p c 3) *
              ((z - GaussianRat.toComplex c) ^ 3 -
                (w - GaussianRat.toComplex c) ^ 3)‖ +
          ‖GaussianRat.toComplex (normalizedCoeff p c 4) *
              ((z - GaussianRat.toComplex c) ^ 4 -
                (w - GaussianRat.toComplex c) ^ 4)‖ := norm_add₃_le
      _ <=
          ((2 * GaussianRat.l1 (normalizedCoeff p c 2) * r : ℚ) : ℝ) *
              ‖z - w‖ +
          ((3 * GaussianRat.l1 (normalizedCoeff p c 3) * r ^ 2 : ℚ) : ℝ) *
              ‖z - w‖ +
          ((4 * GaussianRat.l1 (normalizedCoeff p c 4) * r ^ 3 : ℚ) : ℝ) *
              ‖z - w‖ := add_le_add (add_le_add hterm2 hterm3) hterm4
      _ = (K : ℝ) * dist z w := by
        rw [hKcoe, dist_eq_norm]
        unfold contractionL1
        push_cast
        ring
  have hcenter :
      ‖(toComplexPolynomial p).eval (GaussianRat.toComplex c) /
          GaussianRat.toComplex (linearCoeff p c)‖ +
          (K : ℝ) * (r : ℝ) <= (r : ℝ) := by
    rw [eval_center_div_linear]
    rw [hKcoe]
    calc
      ‖GaussianRat.toComplex (normalizedCoeff p c 0)‖ +
            (contractionL1 p c r : ℝ) * (r : ℝ) <=
          (GaussianRat.l1 (normalizedCoeff p c 0) : ℝ) +
            (contractionL1 p c r : ℝ) * (r : ℝ) :=
        add_le_add (GaussianRat.norm_toComplex_le_l1 _) le_rfl
      _ = (displacementL1 p c + contractionL1 p c r * r : ℚ) := by
        simp [displacementL1]
      _ <= (r : ℝ) := by exact_mod_cast hstep
  obtain ⟨z, hz, hpz⟩ :=
    GaussianPolynomialContraction.exists_zero_in_closedBall
      (toComplexPolynomial p) (GaussianRat.toComplex c)
      (GaussianRat.toComplex (linearCoeff p c)) hA
      (r : ℝ) hrR K hK hLip hcenter
  exact ⟨z, hz, by
    rw [evalComplex_eq_toComplexPolynomial_eval]
    exact hpz⟩

/-- The radius-free certificate yields a root in its automatically computed
disk. -/
theorem autoValid_exists_zero_in_closedBall {p : QPoly4} {c : GaussianRat}
    (h : AutoValid p c) :
    ∃ z ∈ closedBall (GaussianRat.toComplex c) (newtonRadius p c : ℝ),
      evalComplex p z = 0 :=
  isValid_exists_zero_in_closedBall (autoValid_isValid h)

end GaussianPolynomialContractionCertificate

end LeanProofs.PolynomialFormulas
