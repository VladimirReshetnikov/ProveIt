import OAI.Combinatorics.Progressions.Estimates.CoefficientRowEvaluation

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {K V : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (p : ∀ j, VectorPolynomial V ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (p j) d ∈ U j)

noncomputable def centeredAffineCoefficientArray (center : ∀ j, U j) (frame : Option K → V → ℝ) :
    CoefficientArray (K := K) U :=
  affineSampleCoefficientArray U p hm frame - constantCoefficientArray U (fun s => center s.1)

noncomputable def centeredAffineCoefficientTorus (center : ∀ j, U j) (frame : Option K → V → ℝ) :
    CoefficientTorus (K := K) U :=
  QuotientAddGroup.mk' (coefficientIntegerLattice U) (centeredAffineCoefficientArray U p hm center frame)

theorem coefficientRowPolynomial_centered_affine_eval
    (hp : ∀ j, DegreeLE (1 : V → ℕ) (j.val + 1) (p j))
    (center : ∀ j, U j) (frame : Option K → V → ℝ) (j : Fin m) (i : J j) (x : K → ℝ) :
    MvPolynomial.eval x
        (coefficientRowPolynomial U (centeredAffineCoefficientArray U p hm center frame) j i) =
      eval (fun v => frame none v + ∑ k, frame (some k) v * x k) (p j) i - (center j).val i := by
  rw [centeredAffineCoefficientArray, coefficientRowPolynomial_sub, map_sub,
    coefficientRowPolynomial_constant, MvPolynomial.eval_C,
    coefficientRowPolynomial_affine_eval U p hp hm]

end Erdos3.VectorPolynomial

end

end OAI
