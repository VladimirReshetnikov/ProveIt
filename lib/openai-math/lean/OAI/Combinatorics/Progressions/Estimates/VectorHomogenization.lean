import Mathlib.LinearAlgebra.Finsupp.LSum
import OAI.Combinatorics.Progressions.Polynomial.AdaptedPolynomialSubstitution
import OAI.Combinatorics.Progressions.Polynomial.HomogenizingMonomial

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators TensorProduct

theorem homogeneous_finset_sum {I A R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
    {h : ℕ} (s : Finset A) (p : A → VectorPolynomial I R W)
    (hp : ∀ a ∈ s, Homogeneous h (p a)) : Homogeneous h (∑ a ∈ s, p a) := by
  intro d hd
  simp only [map_sum, Finsupp.finsetSum_apply]
  exact Finset.sum_eq_zero (fun a ha => hp a ha d hd)

theorem homogeneous_substitute_linear {I K R W : Type*} [CommRing R]
    [AddCommGroup W] [Module R W] {h : ℕ}
    (f : I → MvPolynomial K R) (hf : ∀ i, (f i).IsHomogeneous 1)
    (p : VectorPolynomial I R W) (hp : Homogeneous h p) :
    Homogeneous h (substitute f p) := by
  classical
  rw [← sum_monomial_coefficients p, Finsupp.sum, map_sum]
  apply homogeneous_finset_sum
  intro d hd
  rw [monomial, substitute_tmul]
  apply homogeneous_tmul
  have hm := MvPolynomial.isHomogeneous_monomial (1 : R) (homogeneous_support_degree hp hd)
  simpa only [MvPolynomial.aeval_def, MvPolynomial.algebraMap_eq, Nat.one_mul] using
    hm.eval₂ MvPolynomial.C f (fun r => MvPolynomial.isHomogeneous_C K r) hf

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators TensorProduct

noncomputable def homogenize {I R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
    (h : ℕ) : VectorPolynomial I R W →ₗ[R] VectorPolynomial (Option I) R W :=
  (Finsupp.lsum R (fun d => TensorProduct.mk R (MvPolynomial (Option I) R) W
    (homogenizingMonomial h d))).comp coefficients.toLinearMap

theorem homogenize_apply {I R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
    (h : ℕ) (p : VectorPolynomial I R W) :
    homogenize h p = ∑ d ∈ (coefficients p).support,
      homogenizingMonomial h d ⊗ₜ[R] coefficients p d := by
  simp only [homogenize, LinearMap.comp_apply, LinearEquiv.coe_coe, Finsupp.lsum_apply,
    Finsupp.sum, TensorProduct.mk_apply]

theorem dehomogenize_homogenize {I R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
    (h : ℕ) (p : VectorPolynomial I R W) :
    substitute dehomogenizingSubstitution (homogenize h p) = p := by
  rw [homogenize_apply, map_sum]
  simp only [substitute_tmul, homogenizingMonomial_dehomogenize]
  exact sum_monomial_coefficients p

theorem homogenize_homogeneous {I R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
    (h : ℕ) (p : VectorPolynomial I R W) (hp : DegreeLE (1 : I → ℕ) h p) :
    Homogeneous h (homogenize h p) := by
  rw [homogenize_apply]
  apply homogeneous_finset_sum
  intro d hd
  have hb : d.degree ≤ h := by
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using
      (degreeLE_iff (1 : I → ℕ) h p).mp hp d hd
  exact homogeneous_tmul (homogenizingMonomial_homogeneous h d hb) _

theorem eval_homogenize {I R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
    (h : ℕ) (p : VectorPolynomial I R W) (x : I → R) :
    eval (fun i : Option I => i.elim 1 x) (homogenize h p) = eval x p := by
  have he := congrArg (eval x) (dehomogenize_homogenize h p)
  rw [eval_substitute] at he
  convert he using 1
  apply congrArg (fun y => eval y (homogenize h p))
  funext i
  cases i <;> simp [dehomogenizingSubstitution]

end Erdos3.VectorPolynomial

end

end OAI
