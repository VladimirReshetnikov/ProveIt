import Surreal.Algebra.PolynomialRootNormalization
import Surreal.Foundations.SignSequenceSimpleRootLifting
import Surreal.Foundations.SignSequenceRelativeAsymptotics

/-!
# Actual finite root normalization

This supplies the scaled polynomial existence step of
`trigonometry:thm:stability`. A finite constant term, residue-one linear
term and infinitesimal higher coefficients give a unique finite simple
root. Explicit scaling transports it to the original polynomial, retaining
its native multiplicity. The rational trigonometric chart is separate.
-/

universe u

namespace Surreal.Foundations.SignSequence

open Polynomial FinitePolynomial

noncomputable section

/-- Every finite root of a polynomial with linear reduction has the forced residue. -/
theorem standardPart_of_linear_reduction_root (P : Polynomial SignSequence.{u})
    (hP : ∀ n, IsFinite (P.coeff n)) (b : ℝ) (hred : reducePolynomial P hP = X + C b)
    (y : SignSequence.{u}) (hy : IsFinite y) (hyr : P.IsRoot y) : standardPart y = -b := by
  let y' : FiniteElement.{u} := ⟨y, hy⟩
  have hr : (finitePolynomial P hP).IsRoot y' := by
    apply Polynomial.IsRoot.of_map (f := finiteElementInclusion) _ finiteElementInclusion_injective
    simpa only [map_finitePolynomial, finiteElementInclusion_apply] using hyr
  have hh := hr.map (f := standardPartHom.toRingHom)
  change (reducePolynomial P hP).IsRoot (standardPart y) at hh
  apply eq_neg_iff_add_eq_zero.mpr
  simpa only [hred, IsRoot.def, eval_add, eval_X, eval_C] using hh

/-- Finiteness of the normalized coefficients only needs a finite scale ratio.
This variant is used on the larger open neighborhood of a simple root. -/
theorem rootNormalization_finite_of_finite_ratio (P : Polynomial SignSequence.{u})
    (A l : SignSequence.{u}) (hl : l ≠ 0) (hlf : IsFinite l) (hla : IsFinite (l / A))
    (h0 : IsFinite (P.coeff 0 / (A * l))) (h1 : IsFinite (P.coeff 1 / A))
    (hh : ∀ n, IsFinite (P.coeff (n + 2))) :
    ∀ n, IsFinite ((rootNormalization P A l).coeff n)
  | 0 => by simpa only [rootNormalization_coeff_zero] using h0
  | 1 => by simpa only [rootNormalization_coeff_one P A l hl] using h1
  | n + 2 => by
    rw [rootNormalization_coeff_add_two P A l hl]
    exact finite_mul (finite_mul (hh n) hla) (finite_pow hlf n)

section Normalization

variable (P : Polynomial SignSequence.{u}) (A l : SignSequence.{u})
  (hl : l ≠ 0) (hlf : IsFinite l) (hla : IsInfinitesimal (l / A))
  (h0 : IsFinite (P.coeff 0 / (A * l)))
  (h1 : IsInfinitesimal (P.coeff 1 / A - 1))
  (hh : ∀ n, IsFinite (P.coeff (n + 2)))

include hl hlf hla hh

/-- Every higher coefficient acquires the infinitesimal factor `λ/A`. -/
theorem rootNormalization_high_infinitesimal (n : ℕ) :
    IsInfinitesimal ((rootNormalization P A l).coeff (n + 2)) := by
  rw [rootNormalization_coeff_add_two P A l hl]
  exact infinitesimal_mul_finite (finite_mul_infinitesimal (hh n) hla) (finite_pow hlf n)

include h0 h1

/-- The normalized polynomial has finite coefficients in every degree. -/
theorem rootNormalization_finite : ∀ n, IsFinite ((rootNormalization P A l).coeff n)
  | 0 => by simpa only [rootNormalization_coeff_zero] using h0
  | 1 => by
    rw [rootNormalization_coeff_one P A l hl]
    exact finite_of_infinitesimal_sub_one h1
  | n + 2 => finite_of_infinitesimal (rootNormalization_high_infinitesimal P A l hl hlf hla hh n)

/-- Reduction is literally `Y + st(P(0)/(Aλ))`; no hidden analytic remainder is assumed. -/
theorem rootNormalization_reduction :
    reducePolynomial (rootNormalization P A l)
      (rootNormalization_finite P A l hl hlf hla h0 h1 hh) =
        X + C (standardPart (P.coeff 0 / (A * l))) := by
  apply Polynomial.ext
  intro n
  rw [reducePolynomial_coeff]
  rcases n with _ | n
  · simp
  rcases n with _ | n
  · rw [rootNormalization_coeff_one P A l hl,
      standardPart_eq_one_of_infinitesimal_sub_one h1]
    simp
  · have hi := rootNormalization_high_infinitesimal P A l hl hlf hla hh n
    rw [(standardPart_eq_zero_iff (finite_of_infinitesimal hi)).mpr hi]
    simp [coeff_X]

/-- A unique simple root exists throughout the whole closed scale ball `h/λ ∈ O`. -/
theorem exists_unique_root_at_scale (hA : A ≠ 0) :
    ∃ h : SignSequence.{u}, IsFinite (h / l) ∧ P.IsRoot h ∧ P.rootMultiplicity h = 1 ∧
      ∀ k, IsFinite (k / l) → P.IsRoot k → k = h := by
  let N := rootNormalization P A l
  have hN := rootNormalization_finite P A l hl hlf hla h0 h1 hh
  have hred := rootNormalization_reduction P A l hl hlf hla h0 h1 hh
  obtain ⟨y, hy, hys, hyr, hym, hu⟩ :=
    exists_unique_simple_root_of_linear_reduction N hN _ hred
  have hN0 : N ≠ 0 := by
    intro he
    simp only [he, rootMultiplicity_zero] at hym
    exact Nat.zero_ne_one hym
  refine ⟨l * y, ?_, (isRoot_rootNormalization_iff P A l y hA hl).mp hyr, ?_, ?_⟩
  · simpa only [mul_div_cancel_left₀ y hl] using hy
  · rw [← rootMultiplicity_rootNormalization P A l y hl hN0]
    exact hym
  · intro k hk hkr
    have hkn : N.IsRoot (k / l) :=
      (isRoot_rootNormalization_iff P A l (k / l) hA hl).mpr (by
        simpa only [mul_div_cancel₀ k hl] using hkr)
    have hks := standardPart_of_linear_reduction_root N hN _ hred (k / l) hk hkn
    have he := hu (k / l) hk hkn hks
    rw [← he, mul_div_cancel₀ k hl]

end Normalization
end
end Surreal.Foundations.SignSequence
