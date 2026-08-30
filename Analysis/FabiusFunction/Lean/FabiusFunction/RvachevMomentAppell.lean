import FabiusFunction.AnalyticMoments
import FabiusFunction.AppellSequence
import FabiusFunction.ReciprocalExponentialGenerating
import Mathlib.Topology.Algebra.Polynomial

/-!
# Rvachev moments and Appell deconvolution

This module packages the polynomial deconvolution calculus of Rvachev's
probability density.  The full raw moment sequence inserts zero at every odd
index of the already executable rational even moments.  Its binomial-
convolution reciprocal supplies an Appell family over `ℚ`, which is then
mapped coefficientwise to `ℝ`.

The analytic bridge is finite throughout.  Expanding an Appell polynomial at
`x + y` and integrating its powers against `rvachevUp` turns the integral into
the binomial convolution of the raw moment sequence with its reciprocal.
Consequently the Appell polynomial of index `n` smooths exactly to `x ^ n`.
Extending this construction coefficientwise gives a deconvolution operator on
arbitrary real polynomials; smoothing its output against `rvachevUp` recovers
the original polynomial exactly.
-/

set_option autoImplicit false

open MeasureTheory Polynomial

namespace Fabius

/-- The full rational raw-moment sequence of Rvachev's probability density.
At an even index `2n` it is the executable moment `moment n`; at an odd index
it is zero. -/
def rvachevRawMomentRat (r : ℕ) : ℚ :=
  if 2 ∣ r then moment (r / 2) else 0

/-- The zeroth raw Rvachev moment is one. -/
@[simp]
theorem rvachevRawMomentRat_zero : rvachevRawMomentRat 0 = 1 := by
  simp [rvachevRawMomentRat, moment_zero]

/-- The full raw-moment sequence restricts at even indices to `moment`. -/
@[simp]
theorem rvachevRawMomentRat_even (n : ℕ) :
    rvachevRawMomentRat (2 * n) = moment n := by
  simp [rvachevRawMomentRat]

/-- Every odd entry of the full raw-moment sequence vanishes. -/
@[simp]
theorem rvachevRawMomentRat_odd (n : ℕ) :
    rvachevRawMomentRat (2 * n + 1) = 0 := by
  simp [rvachevRawMomentRat, Nat.not_two_dvd_bit1]

/-- The reciprocal exponential-generating sequence of the rational raw
Rvachev moments.  Equivalently, these are the complete Bell polynomials in
the negatives of the raw-moment cumulants. -/
noncomputable def rvachevReciprocalMomentRat : ℕ → ℚ :=
  Bell.reciprocal rvachevRawMomentRat

/-- The reciprocal Rvachev moment sequence is normalized at zero. -/
@[simp]
theorem rvachevReciprocalMomentRat_zero :
    rvachevReciprocalMomentRat 0 = 1 := by
  simp [rvachevReciprocalMomentRat]

/-- The rational raw moments and their reciprocal convolve to the unit
sequence for exponential generating functions. -/
theorem binomialConv_rvachevRawMomentRat_reciprocal :
    Bell.binomialConv rvachevRawMomentRat rvachevReciprocalMomentRat =
      Bell.unitSeq ℚ := by
  exact Bell.binomialConv_reciprocal rvachevRawMomentRat
    rvachevRawMomentRat_zero

/-- The reciprocal Rvachev moments are the complete Bell polynomials in the
negatives of the formal cumulants of the raw moment sequence. -/
theorem rvachevReciprocalMomentRat_eq_completeBellPolynomial :
    rvachevReciprocalMomentRat =
      completeBellPolynomial (-momentCumulant rvachevRawMomentRat) := by
  exact reciprocal_eq_completeBellPolynomial rvachevRawMomentRat
    rvachevRawMomentRat_zero

/-- The rational Appell polynomial associated with the reciprocal Rvachev
moment sequence. -/
noncomputable def rvachevAppellPolynomialRat (n : ℕ) : ℚ[X] :=
  Appell.poly rvachevReciprocalMomentRat n

/-- Every rational Rvachev--Appell polynomial is monic. -/
theorem monic_rvachevAppellPolynomialRat (n : ℕ) :
    (rvachevAppellPolynomialRat n).Monic := by
  exact Appell.monic_poly rvachevReciprocalMomentRat_zero n

/-- The rational Rvachev--Appell polynomial of index `n` has degree exactly
`n`. -/
@[simp]
theorem natDegree_rvachevAppellPolynomialRat (n : ℕ) :
    (rvachevAppellPolynomialRat n).natDegree = n := by
  exact Appell.natDegree_poly rvachevReciprocalMomentRat_zero n

/-- The real Rvachev--Appell polynomial obtained by casting the rational
coefficients. -/
noncomputable def rvachevAppellPolynomial (n : ℕ) : ℝ[X] :=
  (rvachevAppellPolynomialRat n).map (Rat.castHom ℝ)

/-- Casting the rational Appell polynomial is the Appell construction on the
coefficientwise-cast reciprocal sequence. -/
theorem rvachevAppellPolynomial_eq_poly_cast (n : ℕ) :
    rvachevAppellPolynomial n =
      Appell.poly (fun r ↦ (rvachevReciprocalMomentRat r : ℝ)) n := by
  ext j
  rw [rvachevAppellPolynomial, rvachevAppellPolynomialRat,
    Polynomial.coeff_map, Appell.coeff_poly, Appell.coeff_poly]
  by_cases hj : j ≤ n
  · rw [if_pos hj, if_pos hj]
    norm_num
  · rw [if_neg hj, if_neg hj]
    simp

/-- Every real Rvachev--Appell polynomial is monic. -/
theorem monic_rvachevAppellPolynomial (n : ℕ) :
    (rvachevAppellPolynomial n).Monic := by
  rw [rvachevAppellPolynomial_eq_poly_cast]
  exact Appell.monic_poly (by simp) n

/-- The real Rvachev--Appell polynomial of index `n` has degree exactly `n`. -/
@[simp]
theorem natDegree_rvachevAppellPolynomial (n : ℕ) :
    (rvachevAppellPolynomial n).natDegree = n := by
  rw [rvachevAppellPolynomial_eq_poly_cast]
  exact Appell.natDegree_poly (by simp) n

/-- The Appell addition formula specialized to the real Rvachev family. -/
theorem eval_rvachevAppellPolynomial_add (n : ℕ) (x y : ℝ) :
    (rvachevAppellPolynomial n).eval (x + y) =
      ∑ k ∈ Finset.range (n + 1),
        (n.choose k : ℝ) *
          (rvachevAppellPolynomial (n - k)).eval x * y ^ k := by
  let b : ℕ → ℝ := fun r ↦ (rvachevReciprocalMomentRat r : ℝ)
  have htranslate := Appell.poly_translate b x n
  have heval := congrArg (fun p : ℝ[X] ↦ p.eval y) htranslate
  rw [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_C, Appell.eval_poly_eq_sum] at heval
  simp only [Appell.translate] at heval
  rw [rvachevAppellPolynomial_eq_poly_cast]
  simp_rw [rvachevAppellPolynomial_eq_poly_cast]
  calc
    (Appell.poly b n).eval (x + y) =
        (Appell.poly b n).eval (y + x) := by rw [add_comm]
    _ = _ := heval.symm

/-- The analytic raw moment of every order is the cast of the executable
rational raw-moment sequence. -/
theorem integral_pow_mul_rvachev_eq_rvachevRawMomentRat_cast
    (F : BoundedFabius) (hF : IsFabius F) (r : ℕ) :
    (∫ y : ℝ, y ^ r * rvachevUp F y) = (rvachevRawMomentRat r : ℝ) := by
  obtain ⟨n, hn | hn⟩ := Nat.even_or_odd' r
  · subst r
    rw [rvachevRawMomentRat_even,
      integral_even_pow_mul_rvachev_eq_moment F hF n]
  · subst r
    rw [rvachevRawMomentRat_odd,
      integral_odd_pow_mul_rvachev_eq_zero F hF n]
    simp

private theorem hasCompactSupport_rvachevUp
    (F : BoundedFabius) (hF : IsFabius F) :
    HasCompactSupport (rvachevUp F) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    ((support_rvachev_subset_Ioo F hF).trans Set.Ioo_subset_Icc_self)

private theorem integrable_pow_mul_rvachev
    (F : BoundedFabius) (hF : IsFabius F) (r : ℕ) :
    Integrable (fun y : ℝ ↦ y ^ r * rvachevUp F y) := by
  exact ((continuous_pow r).mul (rvachev_contDiff F hF).continuous)
    |>.integrable_of_hasCompactSupport
      ((hasCompactSupport_rvachevUp F hF).mul_left)

/-- Smoothing a Rvachev--Appell polynomial by the translated up density
recovers the corresponding monomial exactly. -/
theorem integral_eval_rvachevAppellPolynomial_add_mul_rvachev
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) (x : ℝ) :
    (∫ y : ℝ,
      (rvachevAppellPolynomial n).eval (x + y) * rvachevUp F y) = x ^ n := by
  let m : ℕ → ℝ := fun r ↦ (rvachevRawMomentRat r : ℝ)
  let b : ℕ → ℝ := fun r ↦ (rvachevReciprocalMomentRat r : ℝ)
  have hconv : Bell.binomialConv m b = Bell.unitSeq ℝ := by
    funext r
    calc
      Bell.binomialConv m b r =
          ((Bell.binomialConv rvachevRawMomentRat
            rvachevReciprocalMomentRat r : ℚ) : ℝ) := by
        exact Bell.binomialConv_map (Rat.castHom ℝ)
          rvachevRawMomentRat rvachevReciprocalMomentRat r
      _ = (Bell.unitSeq ℚ r : ℝ) := by
        rw [congrFun binomialConv_rvachevRawMomentRat_reciprocal r]
      _ = Bell.unitSeq ℝ r := by cases r <;> simp [Bell.unitSeq]
  have hpoint : (fun y : ℝ ↦
      (rvachevAppellPolynomial n).eval (x + y) * rvachevUp F y) =
      fun y : ℝ ↦ ∑ k ∈ Finset.range (n + 1),
        ((n.choose k : ℝ) *
          (rvachevAppellPolynomial (n - k)).eval x) *
            (y ^ k * rvachevUp F y) := by
    funext y
    rw [eval_rvachevAppellPolynomial_add, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _hk
    ring
  rw [hpoint, MeasureTheory.integral_finsetSum _ fun k _hk ↦
    (integrable_pow_mul_rvachev F hF k).const_mul _]
  simp_rw [MeasureTheory.integral_const_mul,
    integral_pow_mul_rvachev_eq_rvachevRawMomentRat_cast F hF]
  have hrepro := Appell.sum_choose_eval_poly hconv x n
  calc
    (∑ k ∈ Finset.range (n + 1),
        ((n.choose k : ℝ) *
          (rvachevAppellPolynomial (n - k)).eval x) *
            (rvachevRawMomentRat k : ℝ)) =
      ∑ k ∈ Finset.range (n + 1),
        (n.choose k : ℝ) *
          (m k * (Appell.poly b (n - k)).eval x) := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [rvachevAppellPolynomial_eq_poly_cast]
      dsimp [m, b]
      ring
    _ = x ^ n := hrepro

/-- Polynomial deconvolution by the Rvachev moment law: replace every monomial
`X ^ n` in `P` by the reciprocal-moment Appell polynomial of index `n`. -/
noncomputable def rvachevDeconvolvedPolynomial (P : ℝ[X]) : ℝ[X] :=
  P.sum fun n a ↦ C a * rvachevAppellPolynomial n

/-- Polynomial deconvolution by the Rvachev moment law, packaged as a real
linear map.  On the monomial coefficient of degree `n`, it sends `a` to
`C a * rvachevAppellPolynomial n`.  Its underlying function is definitionally
the existing `rvachevDeconvolvedPolynomial`. -/
noncomputable def rvachevDeconvolutionLinearMap : ℝ[X] →ₗ[ℝ] ℝ[X] :=
  Polynomial.lsum fun n ↦
    (LinearMap.mulRight ℝ (rvachevAppellPolynomial n)).comp
      (Polynomial.CAlgHom : ℝ →ₐ[ℝ] ℝ[X]).toLinearMap

/-- Applying the linear-map package for Rvachev deconvolution is the original
polynomial deconvolution operation. -/
@[simp]
theorem rvachevDeconvolutionLinearMap_apply (P : ℝ[X]) :
    rvachevDeconvolutionLinearMap P = rvachevDeconvolvedPolynomial P := by
  rfl

/-- Rvachev polynomial deconvolution sends zero to zero. -/
@[simp]
theorem rvachevDeconvolvedPolynomial_zero :
    rvachevDeconvolvedPolynomial (0 : ℝ[X]) = 0 := by
  simpa only [rvachevDeconvolutionLinearMap_apply] using
    rvachevDeconvolutionLinearMap.map_zero

/-- Rvachev polynomial deconvolution preserves addition. -/
@[simp]
theorem rvachevDeconvolvedPolynomial_add (P Q : ℝ[X]) :
    rvachevDeconvolvedPolynomial (P + Q) =
      rvachevDeconvolvedPolynomial P + rvachevDeconvolvedPolynomial Q := by
  simpa only [rvachevDeconvolutionLinearMap_apply] using
    rvachevDeconvolutionLinearMap.map_add P Q

/-- Rvachev polynomial deconvolution commutes with real scalar
multiplication. -/
@[simp]
theorem rvachevDeconvolvedPolynomial_smul (a : ℝ) (P : ℝ[X]) :
    rvachevDeconvolvedPolynomial (a • P) =
      a • rvachevDeconvolvedPolynomial P := by
  simpa only [rvachevDeconvolutionLinearMap_apply] using
    rvachevDeconvolutionLinearMap.map_smul a P

/-- Rvachev polynomial deconvolution commutes with finite polynomial sums. -/
@[simp]
theorem rvachevDeconvolvedPolynomial_finsetSum
    {ι : Type*} (s : Finset ι) (P : ι → ℝ[X]) :
    rvachevDeconvolvedPolynomial (∑ i ∈ s, P i) =
      ∑ i ∈ s, rvachevDeconvolvedPolynomial (P i) := by
  simpa only [rvachevDeconvolutionLinearMap_apply] using
    map_sum rvachevDeconvolutionLinearMap P s

/-- Multiplication by a constant polynomial can be pulled through Rvachev
polynomial deconvolution. -/
@[simp]
theorem rvachevDeconvolvedPolynomial_C_mul (a : ℝ) (P : ℝ[X]) :
    rvachevDeconvolvedPolynomial (C a * P) =
      C a * rvachevDeconvolvedPolynomial P := by
  simpa only [Polynomial.smul_eq_C_mul] using
    rvachevDeconvolvedPolynomial_smul a P

/-- Rvachev polynomial deconvolution does not raise degree. -/
theorem natDegree_rvachevDeconvolvedPolynomial_le (P : ℝ[X]) :
    (rvachevDeconvolvedPolynomial P).natDegree ≤ P.natDegree := by
  rw [rvachevDeconvolvedPolynomial, Polynomial.sum_def]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro n hn
  exact (Polynomial.natDegree_C_mul_le _ _).trans <|
    (natDegree_rvachevAppellPolynomial n).le.trans
      (Polynomial.le_natDegree_of_mem_supp n hn)

private theorem integrable_eval_rvachevAppellPolynomial_add_mul_rvachev
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) (x : ℝ) :
    Integrable (fun y : ℝ ↦
      (rvachevAppellPolynomial n).eval (x + y) * rvachevUp F y) := by
  exact (((rvachevAppellPolynomial n).continuous.comp
      (continuous_const.add continuous_id)).mul
        (rvachev_contDiff F hF).continuous)
    |>.integrable_of_hasCompactSupport
      ((hasCompactSupport_rvachevUp F hF).mul_left)

/-- Smoothing a deconvolved real polynomial against the translated up density
recovers the original polynomial exactly. -/
theorem integral_eval_rvachevDeconvolvedPolynomial_add_mul_rvachev
    (F : BoundedFabius) (hF : IsFabius F) (P : ℝ[X]) (x : ℝ) :
    (∫ y : ℝ,
      (rvachevDeconvolvedPolynomial P).eval (x + y) * rvachevUp F y) =
        P.eval x := by
  have hpoint : (fun y : ℝ ↦
      (rvachevDeconvolvedPolynomial P).eval (x + y) * rvachevUp F y) =
      fun y : ℝ ↦ ∑ n ∈ P.support,
        P.coeff n *
          ((rvachevAppellPolynomial n).eval (x + y) * rvachevUp F y) := by
    funext y
    rw [rvachevDeconvolvedPolynomial, Polynomial.eval_sum,
      Polynomial.sum_def, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n _hn
    simp only [Polynomial.eval_mul, Polynomial.eval_C]
    ring
  rw [hpoint, MeasureTheory.integral_finsetSum _ fun n _hn ↦
    (integrable_eval_rvachevAppellPolynomial_add_mul_rvachev F hF n x)
      |>.const_mul _]
  simp_rw [MeasureTheory.integral_const_mul,
    integral_eval_rvachevAppellPolynomial_add_mul_rvachev F hF]
  simpa only [Polynomial.sum_def] using
    (Polynomial.eval_eq_sum (p := P) (x := x)).symm

end Fabius
