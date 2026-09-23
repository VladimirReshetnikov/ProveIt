import Surreal.Surcomplex.FiniteTrigonometry
import Surreal.Algebra.TrigonometricTaylor
import Surreal.Foundations.SignSequenceStrongRegroup
import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# The separate strong Taylor sums for finite sine and cosine

The real and imaginary parts of the actual infinitesimal exponential are
the even cosine and odd sine strong sums. Injective reindexing removes only
zero terms, with joint Hahn summability retained. The finite phase then
identifies the existing coordinate definitions with the two recentered
Taylor formulas in `trigonometry:eq:sinfinite` and `trigonometry:eq:cosfinite`.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

noncomputable section

/-- Multiplication of a real infinitesimal by the imaginary unit is infinitesimal. -/
theorem infinitesimal_ofReal_mul_I (ε : SignSequence.{u})
    (hε : SignSequence.IsInfinitesimal ε) : IsInfinitesimal (ofReal ε * I) := by
  constructor
  · simp
  · simpa using hε

private theorem factorial_coefficient (n : ℕ) :
    (ofComplex (algebraMap ℚ ℂ (1 / (n.factorial : ℚ))) : Surcomplex.{u}) =
      ofReal (SignSequence.ofReal (1 / (n.factorial : ℝ))) := by
  rw [← ofComplex_ofReal]
  congr 1
  push_cast
  simp

private theorem exp_even_term (ε : SignSequence.{u}) (n : ℕ) :
    ofComplex (algebraMap ℚ ℂ (1 / ((2 * n).factorial : ℚ))) * (ofReal ε * I) ^ (2 * n) =
      ofReal (SignSequence.ofReal ((-1 : ℝ) ^ n / (2 * n).factorial) * ε ^ (2 * n)) := by
  have hI : (I : Surcomplex.{u}) ^ (2 * n) = (-1) ^ n := by rw [pow_mul, I_sq]
  rw [factorial_coefficient, mul_pow, hI, map_mul, map_pow]
  have hneg : (-1 : Surcomplex.{u}) ^ n = ofReal (SignSequence.ofReal ((-1 : ℝ) ^ n)) := by
    simp
  rw [hneg]
  simp only [map_div₀, map_inv₀, map_pow, map_neg, map_one, map_natCast, one_div]
  ring

private theorem exp_odd_term (ε : SignSequence.{u}) (n : ℕ) :
    ofComplex (algebraMap ℚ ℂ (1 / ((2 * n + 1).factorial : ℚ))) *
        (ofReal ε * I) ^ (2 * n + 1) =
      ofReal (SignSequence.ofReal ((-1 : ℝ) ^ n / (2 * n + 1).factorial) *
        ε ^ (2 * n + 1)) * I := by
  have hI : (I : Surcomplex.{u}) ^ (2 * n + 1) = (-1) ^ n * I := by
    rw [pow_succ, pow_mul, I_sq]
  rw [factorial_coefficient, mul_pow, hI, map_mul, map_pow]
  have hneg : (-1 : Surcomplex.{u}) ^ n = ofReal (SignSequence.ofReal ((-1 : ℝ) ^ n)) := by
    simp
  rw [hneg]
  simp only [map_div₀, map_inv₀, map_pow, map_neg, map_one, map_natCast, one_div]
  ring

/-- The separate even Taylor family for cosine is strongly summable. -/
theorem stronglySummable_cosTaylor (ε : SignSequence.{u})
    (hε : SignSequence.IsInfinitesimal ε) :
    SignSequence.StronglySummable (fun n : ℕ =>
      SignSequence.ofReal ((-1 : ℝ) ^ n / (2 * n).factorial) * ε ^ (2 * n)) := by
  have hf := (stronglySummable_infExp (ofReal ε * I) (infinitesimal_ofReal_mul_I ε hε)).re
  simpa only [exp_even_term, ofReal_re] using
    SignSequence.StronglySummable.comp_injective hf (fun n => 2 * n) (by intro a b h; dsimp at h; omega)

/-- The separate odd Taylor family for sine is strongly summable. -/
theorem stronglySummable_sinTaylor (ε : SignSequence.{u})
    (hε : SignSequence.IsInfinitesimal ε) :
    SignSequence.StronglySummable (fun n : ℕ =>
      SignSequence.ofReal ((-1 : ℝ) ^ n / (2 * n + 1).factorial) * ε ^ (2 * n + 1)) := by
  have hf := (stronglySummable_infExp (ofReal ε * I) (infinitesimal_ofReal_mul_I ε hε)).im
  simpa only [exp_odd_term, mul_im, ofReal_re, ofReal_im, I_re, I_im,
    mul_one, zero_mul, add_zero] using
    SignSequence.StronglySummable.comp_injective hf (fun n => 2 * n + 1) (by intro a b h; dsimp at h; omega)

/-- The literal even strong sum in the source cosine formula. -/
def cosTaylorSum (ε : SignSequence.{u}) (hε : SignSequence.IsInfinitesimal ε) :
    SignSequence.{u} :=
  SignSequence.strongSum (fun n : ℕ =>
    SignSequence.ofReal ((-1 : ℝ) ^ n / (2 * n).factorial) * ε ^ (2 * n))
    (stronglySummable_cosTaylor ε hε)

/-- The literal odd strong sum in the source sine formula. -/
def sinTaylorSum (ε : SignSequence.{u}) (hε : SignSequence.IsInfinitesimal ε) :
    SignSequence.{u} :=
  SignSequence.strongSum (fun n : ℕ =>
    SignSequence.ofReal ((-1 : ℝ) ^ n / (2 * n + 1).factorial) * ε ^ (2 * n + 1))
    (stronglySummable_sinTaylor ε hε)

/-- Projecting the exponential strong sum gives exactly the even cosine sum. -/
theorem infExp_ofReal_mul_I_re (ε : SignSequence.{u})
    (hε : SignSequence.IsInfinitesimal ε) :
    (infExp (ofReal ε * I) (infinitesimal_ofReal_mul_I ε hε)).re = cosTaylorSum ε hε := by
  have hf := (stronglySummable_infExp (ofReal ε * I) (infinitesimal_ofReal_mul_I ε hε)).re
  have hz : ∀ n, n ∉ Set.range (fun k : ℕ => 2 * k) →
      (ofComplex (algebraMap ℚ ℂ (1 / (n.factorial : ℚ))) * (ofReal ε * I) ^ n).re = 0 := by
    intro n hn
    obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' n
    · exact (hn ⟨k, hk.symm⟩).elim
    · rw [hk, exp_odd_term]
      simp only [mul_re, ofReal_re, ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_zero]
  have hs := SignSequence.strongSum_comp_injective hf (fun n => 2 * n) (by intro a b h; dsimp at h; omega) hz
  rw [infExp_eq_strongSum, strongSum_re]
  simpa only [cosTaylorSum, exp_even_term, ofReal_re] using hs.symm

/-- Projecting the exponential strong sum gives exactly the odd sine sum. -/
theorem infExp_ofReal_mul_I_im (ε : SignSequence.{u})
    (hε : SignSequence.IsInfinitesimal ε) :
    (infExp (ofReal ε * I) (infinitesimal_ofReal_mul_I ε hε)).im = sinTaylorSum ε hε := by
  have hf := (stronglySummable_infExp (ofReal ε * I) (infinitesimal_ofReal_mul_I ε hε)).im
  have hz : ∀ n, n ∉ Set.range (fun k : ℕ => 2 * k + 1) →
      (ofComplex (algebraMap ℚ ℂ (1 / (n.factorial : ℚ))) * (ofReal ε * I) ^ n).im = 0 := by
    intro n hn
    obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' n
    · rw [hk, exp_even_term, ofReal_im]
    · exact (hn ⟨k, hk.symm⟩).elim
  have hs := SignSequence.strongSum_comp_injective hf (fun n => 2 * n + 1) (by intro a b h; dsimp at h; omega) hz
  rw [infExp_eq_strongSum, strongSum_im]
  simpa only [sinTaylorSum, exp_odd_term, mul_im, ofReal_re, ofReal_im, I_re, I_im,
    mul_one, zero_mul, add_zero] using hs.symm

/-- The exact recentered cosine Taylor formula for every finite real surreal angle. -/
theorem finiteCos_eq_taylor (θ : SignSequence.FiniteElement.{u}) :
    let r := SignSequence.standardPartHom θ
    let ε := θ.val - SignSequence.ofReal r
    let hε : SignSequence.IsInfinitesimal ε := SignSequence.infinitesimal_sub_standardPart θ.property
    finiteCos θ = SignSequence.ofReal (Real.cos r) * cosTaylorSum ε hε -
      SignSequence.ofReal (Real.sin r) * sinTaylorSum ε hε := by
  dsimp only
  rw [finiteCos, finitePhase_eq_exp_mul_infExp, mul_re, ofComplex_re, ofComplex_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    infExp_ofReal_mul_I_re, infExp_ofReal_mul_I_im]

/-- The exact recentered sine Taylor formula for every finite real surreal angle. -/
theorem finiteSin_eq_taylor (θ : SignSequence.FiniteElement.{u}) :
    let r := SignSequence.standardPartHom θ
    let ε := θ.val - SignSequence.ofReal r
    let hε : SignSequence.IsInfinitesimal ε := SignSequence.infinitesimal_sub_standardPart θ.property
    finiteSin θ = SignSequence.ofReal (Real.sin r) * cosTaylorSum ε hε +
      SignSequence.ofReal (Real.cos r) * sinTaylorSum ε hε := by
  dsimp only
  rw [finiteSin, finitePhase_eq_exp_mul_infExp, mul_im, ofComplex_re, ofComplex_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    infExp_ofReal_mul_I_re, infExp_ofReal_mul_I_im, add_comm]


/-- The separate cosine strong sum is the evaluated ordinary Taylor series at zero. -/
theorem powerSeriesEvaluation_taylor_cos_zero (ε : SignSequence.{u})
    (hε : SignSequence.IsInfinitesimal ε) :
    SignSequence.powerSeriesEvaluation ε hε (Analytic.taylorSeries Real.cos 0) =
      cosTaylorSum ε hε := by
  have hf := SignSequence.stronglySummable_coeff_mul_powers ε hε
    (fun n => (Analytic.taylorSeries Real.cos 0).coeff n)
  have hz : ∀ n, n ∉ Set.range (fun k : ℕ => 2 * k) →
      SignSequence.ofReal ((Analytic.taylorSeries Real.cos 0).coeff n) * ε ^ n = 0 := by
    intro n hn
    obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' n
    · exact (hn ⟨k, hk.symm⟩).elim
    · rw [hk]
      simp only [Analytic.coeff_taylorSeries, Real.iteratedDeriv_odd_cos, Pi.mul_apply,
        Pi.pow_apply, Pi.neg_apply, Pi.one_apply, Real.sin_zero, mul_zero, zero_div,
        map_zero, zero_mul]
  have hs := SignSequence.strongSum_comp_injective hf (fun n => 2 * n)
    (by intro a b h; dsimp at h; omega) hz
  rw [SignSequence.powerSeriesEvaluation_eq_strongSum]
  simpa only [cosTaylorSum, Analytic.coeff_taylorSeries, Real.iteratedDeriv_even_cos,
    Pi.mul_apply, Pi.pow_apply, Pi.neg_apply, Pi.one_apply, Real.cos_zero, mul_one] using hs.symm

/-- The separate sine strong sum is the evaluated ordinary Taylor series at zero. -/
theorem powerSeriesEvaluation_taylor_sin_zero (ε : SignSequence.{u})
    (hε : SignSequence.IsInfinitesimal ε) :
    SignSequence.powerSeriesEvaluation ε hε (Analytic.taylorSeries Real.sin 0) =
      sinTaylorSum ε hε := by
  have hf := SignSequence.stronglySummable_coeff_mul_powers ε hε
    (fun n => (Analytic.taylorSeries Real.sin 0).coeff n)
  have hz : ∀ n, n ∉ Set.range (fun k : ℕ => 2 * k + 1) →
      SignSequence.ofReal ((Analytic.taylorSeries Real.sin 0).coeff n) * ε ^ n = 0 := by
    intro n hn
    obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' n
    · rw [hk]
      simp only [Analytic.coeff_taylorSeries, Real.iteratedDeriv_even_sin, Pi.mul_apply,
        Pi.pow_apply, Pi.neg_apply, Pi.one_apply, Real.sin_zero, mul_zero, zero_div,
        map_zero, zero_mul]
    · exact (hn ⟨k, hk.symm⟩).elim
  have hs := SignSequence.strongSum_comp_injective hf (fun n => 2 * n + 1)
    (by intro a b h; dsimp at h; omega) hz
  rw [SignSequence.powerSeriesEvaluation_eq_strongSum]
  simpa only [sinTaylorSum, Analytic.coeff_taylorSeries, Real.iteratedDeriv_odd_sin,
    Pi.mul_apply, Pi.pow_apply, Pi.neg_apply, Pi.one_apply, Real.cos_zero, mul_one] using hs.symm

end

/-- Prescribing the ordinary Taylor rules on every monad uniquely normalizes the finite pair.
This is `trigonometry:prop:normalization`; the rules already imply ordinary-point agreement. -/
theorem finiteTrigonometry_unique_of_taylor
    (S C : SignSequence.FiniteElement.{u} → SignSequence.{u})
    (hS : ∀ (r : ℝ) (θ : SignSequence.FiniteElement.{u})
      (hε : SignSequence.IsInfinitesimal (θ.val - SignSequence.ofReal r)),
      S θ = SignSequence.ofReal (Real.sin r) * cosTaylorSum (θ.val - SignSequence.ofReal r) hε +
        SignSequence.ofReal (Real.cos r) * sinTaylorSum (θ.val - SignSequence.ofReal r) hε)
    (hC : ∀ (r : ℝ) (θ : SignSequence.FiniteElement.{u})
      (hε : SignSequence.IsInfinitesimal (θ.val - SignSequence.ofReal r)),
      C θ = SignSequence.ofReal (Real.cos r) * cosTaylorSum (θ.val - SignSequence.ofReal r) hε -
        SignSequence.ofReal (Real.sin r) * sinTaylorSum (θ.val - SignSequence.ofReal r) hε) :
    S = finiteSin ∧ C = finiteCos := by
  constructor
  · funext θ
    exact (hS (SignSequence.standardPartHom θ) θ
      (SignSequence.infinitesimal_sub_standardPart θ.property)).trans (finiteSin_eq_taylor θ).symm
  · funext θ
    exact (hC (SignSequence.standardPartHom θ) θ
      (SignSequence.infinitesimal_sub_standardPart θ.property)).trans (finiteCos_eq_taylor θ).symm

end Surreal.Surcomplex
