import Surreal.Surcomplex.FiniteTrigonometry
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

private theorem summable_comp_injective {f : ℕ → SignSequence.{u}}
    (hf : SignSequence.StronglySummable f) (k : ℕ → ℕ) (hk : Function.Injective k) :
    SignSequence.StronglySummable (fun n => f (k n)) := by
  constructor
  · apply hf.1.mono
    exact Set.iUnion_subset fun n => Set.subset_iUnion_of_subset (k n) (Set.Subset.refl _)
  · intro a
    exact (hf.2 a).preimage hk.injOn

private theorem strongSum_comp_injective {f : ℕ → SignSequence.{u}}
    (hf : SignSequence.StronglySummable f) (k : ℕ → ℕ) (hk : Function.Injective k)
    (hzero : ∀ n, n ∉ Set.range k → f n = 0) :
    SignSequence.strongSum (fun n => f (k n)) (summable_comp_injective hf k hk) =
      SignSequence.strongSum f hf := by
  apply SignSequence.rawNormalForm_injective
  rw [SignSequence.rawNormalForm_strongSum, SignSequence.rawNormalForm_strongSum]
  have he : hf.toHahnFamily =
      (summable_comp_injective hf k hk).toHahnFamily.embDomain ⟨k, hk⟩ := by
    apply _root_.HahnSeries.SummableFamily.ext
    intro n
    by_cases hn : n ∈ Set.range k
    · obtain ⟨m, rfl⟩ := hn
      exact (_root_.HahnSeries.SummableFamily.embDomain_image
        (summable_comp_injective hf k hk).toHahnFamily ⟨k, hk⟩ (a := m)).symm
    · rw [_root_.HahnSeries.SummableFamily.embDomain_notin_range
        (summable_comp_injective hf k hk).toHahnFamily ⟨k, hk⟩ hn]
      change SignSequence.rawNormalForm (f n) = 0
      rw [hzero n hn, SignSequence.rawNormalForm_zero]
  rw [he, _root_.HahnSeries.SummableFamily.hsum_embDomain]

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
    summable_comp_injective hf (fun n => 2 * n) (by intro a b h; dsimp at h; omega)

/-- The separate odd Taylor family for sine is strongly summable. -/
theorem stronglySummable_sinTaylor (ε : SignSequence.{u})
    (hε : SignSequence.IsInfinitesimal ε) :
    SignSequence.StronglySummable (fun n : ℕ =>
      SignSequence.ofReal ((-1 : ℝ) ^ n / (2 * n + 1).factorial) * ε ^ (2 * n + 1)) := by
  have hf := (stronglySummable_infExp (ofReal ε * I) (infinitesimal_ofReal_mul_I ε hε)).im
  simpa only [exp_odd_term, mul_im, ofReal_re, ofReal_im, I_re, I_im,
    mul_one, zero_mul, add_zero] using
    summable_comp_injective hf (fun n => 2 * n + 1) (by intro a b h; dsimp at h; omega)

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
  have hs := strongSum_comp_injective hf (fun n => 2 * n) (by intro a b h; dsimp at h; omega) hz
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
  have hs := strongSum_comp_injective hf (fun n => 2 * n + 1) (by intro a b h; dsimp at h; omega) hz
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

end

end Surreal.Surcomplex
