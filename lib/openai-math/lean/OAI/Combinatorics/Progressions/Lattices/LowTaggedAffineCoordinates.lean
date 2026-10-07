import OAI.Combinatorics.Progressions.Polynomial.VectorPolynomialAffineSubspace
import OAI.Combinatorics.Progressions.Sampling.LowTaggedSamplingRank

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MvPolynomial
open scoped BigOperators

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)] {X : Type*}

theorem lowTaggedPolynomial_residueAffine (d : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (q : ℕ) (r : X → ℤ)
    (i : Fin (Fintype.card (LowTaggedIndex J d))) :
    lowTaggedPolynomial J d (fun j => residueAffine q r (poly j)) i =
      residueAffinePolynomial q r (lowTaggedPolynomial J d poly i) := by
  apply MvPolynomial.funext
  intro x
  rw [lowTaggedPolynomial_eval, eval_residueAffine,
    residueAffinePolynomial_eval_real, lowTaggedPolynomial_eval]

theorem lowTaggedPolynomial_centered_residueAffine_homogeneousComponent (d : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (q : ℕ) (r : X → ℤ)
    (c : Fin (Fintype.card (LowTaggedIndex J d)) → ℝ)
    (i : Fin (Fintype.card (LowTaggedIndex J d))) :
    homogeneousComponent (lowTaggedWeight J d i)
        (residueAffinePolynomial q r (lowTaggedPolynomial J d poly i - C (c i))) =
      homogeneousComponent (lowTaggedWeight J d i)
        (lowTaggedPolynomial J d (fun j => residueAffine q r (poly j)) i) := by
  rw [lowTaggedPolynomial_residueAffine]
  have hc : homogeneousComponent (lowTaggedWeight J d i) (C (c i) : MvPolynomial X ℝ) = 0 := by
    apply homogeneousComponent_eq_zero
    simpa using lowTaggedWeight_pos J d i
  simp only [residueAffinePolynomial, map_sub, eval₂Hom_C, hc, sub_zero]

theorem lowTaggedTopPolynomial_centered_residueAffine (d : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (q : ℕ) (r : X → ℤ)
    (c : Fin (Fintype.card (LowTaggedIndex J d)) → ℝ) :
    ofCoordinates (R := ℝ) (Pi.basisFun ℝ _)
        (fun i => homogeneousComponent (lowTaggedWeight J d i)
          (residueAffinePolynomial q r (lowTaggedPolynomial J d poly i - C (c i)))) =
      lowTaggedTopPolynomial J d (fun j => residueAffine q r (poly j)) := by
  unfold lowTaggedTopPolynomial
  congr 1
  funext i
  exact lowTaggedPolynomial_centered_residueAffine_homogeneousComponent J d poly q r c i

theorem lowTaggedTopPolynomial_residueAffine_coeff_mem_iSup (d : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (W : ∀ j, Submodule ℝ (J j → ℝ))
    (hcoeff : ∀ j α, α ≠ 0 → coefficients (poly j) α ∈ W j)
    (q : ℕ) (r : X → ℤ) (α : X →₀ ℕ) :
    coefficients (lowTaggedTopPolynomial J d (fun j => residueAffine q r (poly j))) α ∈
      ⨆ h : Fin d, lowTaggedRetained J d W h :=
  lowTaggedTopPolynomial_coeff_mem_iSup J d (fun j => residueAffine q r (poly j)) W
    (fun j β hβ => coefficients_residueAffine_nonzero_mem (W j) q r (poly j)
      (hcoeff j) β hβ) α

end Erdos3.VectorPolynomial

end

end OAI
