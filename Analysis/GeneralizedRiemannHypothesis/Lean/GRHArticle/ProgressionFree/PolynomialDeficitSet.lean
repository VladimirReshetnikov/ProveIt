import GRHArticle.ProgressionFree.PolynomialDeficitCertificate
import Mathlib.Algebra.Polynomial.Degree.Domain

/-!
# Ratio-progression-free polynomial degree sets
-/

namespace GRHArticle.ProgressionFree

/-- Nonzero polynomials in the degree ball whose deficits lie in the prescribed set. -/
def polynomialDeficitSet {F : Type*} [Semiring F] (A : Set ℕ) (N : ℕ) :
    Set (Polynomial F) :=
  {f | f ≠ 0 ∧ f.natDegree ≤ N ∧ N - f.natDegree ∈ A}

/-- Progression-free degree deficits exclude geometric progressions of polynomial
ratio of positive degree. -/
theorem polynomialDeficitSet_no_ratio_progression {F : Type*} [CommRing F] [IsDomain F]
    {A : Set ℕ} (hA : ThreeAPFree A) (N : ℕ) {f r : Polynomial F}
    (hr : 0 < r.natDegree) :
    ¬ (f ∈ polynomialDeficitSet A N ∧ f * r ∈ polynomialDeficitSet A N ∧
      f * r * r ∈ polynomialDeficitSet A N) := by
  rintro ⟨⟨hf, hfN, hfA⟩, ⟨-, hfrN, hfrA⟩, ⟨-, hfrrN, hfrrA⟩⟩
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hr
  have hfr := Polynomial.natDegree_mul hf hr0
  have hfrr := Polynomial.natDegree_mul (mul_ne_zero hf hr0) hr0
  have hmid : (N - f.natDegree) + (N - (f * r * r).natDegree) =
      (N - (f * r).natDegree) + (N - (f * r).natDegree) := by omega
  have h := hA hfA hfrA hfrrA hmid
  omega

/-- The explicit 74-deficit rule gives a polynomial-ratio progression-free
subset of every degree ball, over any integral domain. -/
theorem polynomialDeficitWitness_no_ratio_progression {F : Type*} [CommRing F] [IsDomain F]
    (N : ℕ) {f r : Polynomial F} (hr : 0 < r.natDegree) :
    ¬ (f ∈ polynomialDeficitSet (polynomialDeficitWitness : Set ℕ) N ∧
      f * r ∈ polynomialDeficitSet (polynomialDeficitWitness : Set ℕ) N ∧
      f * r * r ∈ polynomialDeficitSet (polynomialDeficitWitness : Set ℕ) N) :=
  polynomialDeficitSet_no_ratio_progression threeAPFree_polynomialDeficitWitness N hr

end GRHArticle.ProgressionFree
