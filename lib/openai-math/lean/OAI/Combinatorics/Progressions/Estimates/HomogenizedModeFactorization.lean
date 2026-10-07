import OAI.Combinatorics.Progressions.Polynomial.VectorPolynomialAffineDegree

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem homogeneous_degreeLE {I R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
    {h : ℕ} {p : VectorPolynomial I R W} (hp : Homogeneous h p) : DegreeLE (1 : I → ℕ) h p := by
  apply (degreeLE_iff _ _ _).mpr
  intro d hd
  have he := homogeneous_support_degree hp hd
  simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using he.le

theorem dehomogenize_degreeLE {I R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
    {h : ℕ} {p : VectorPolynomial (Option I) R W} (hp : Homogeneous h p) :
    DegreeLE (1 : I → ℕ) h (substitute dehomogenizingSubstitution p) := by
  classical
  apply degreeLE_substitute_affine _ _ p (homogeneous_degreeLE hp)
  intro i
  cases i with
  | none => simp [dehomogenizingSubstitution]
  | some i =>
    change (MvPolynomial.monomial (Finsupp.single i 1) (1 : R)).totalDegree ≤ 1
    simpa using MvPolynomial.totalDegree_monomial_le (Finsupp.single i 1) (1 : R)

theorem siteEvaluation_homogenize {I S R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
    (site : S → I → R) (h : ℕ) (p : VectorPolynomial I R W) :
    siteEvaluation (fun s (i : Option I) => i.elim 1 (site s)) (homogenize h p) = siteEvaluation site p := by
  funext s
  exact eval_homogenize h p (site s)

theorem siteEvaluation_dehomogenize {I S R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
    (site : S → I → R) (p : VectorPolynomial (Option I) R W) :
    siteEvaluation site (substitute dehomogenizingSubstitution p) =
      siteEvaluation (fun s (i : Option I) => i.elim 1 (site s)) p := by
  funext s
  change eval (site s) (substitute dehomogenizingSubstitution p) = _
  rw [eval_substitute]
  apply congrArg (fun x => eval x p)
  funext i
  cases i <;> simp [dehomogenizingSubstitution]

theorem homogeneous_site_factorization_iff {I S R W : Type*}
    [CommRing R] [AddCommGroup W] [Module R W]
    (h : ℕ) (site : S → I → R) (Λ : VectorPolynomial I R W →ₗ[R] R)
    (M : (S → W) →ₗ[R] R) :
    (∀ p, Homogeneous h p → Λ (substitute dehomogenizingSubstitution p) =
      M (siteEvaluation (fun s (i : Option I) => i.elim 1 (site s)) p)) ↔
    (∀ p, DegreeLE (1 : I → ℕ) h p → Λ p = M (siteEvaluation site p)) := by
  constructor
  · intro hf p hp
    have he := hf (homogenize h p) (homogenize_homogeneous h p hp)
    rwa [dehomogenize_homogenize, siteEvaluation_homogenize] at he
  · intro hf p hp
    have he := hf (substitute dehomogenizingSubstitution p) (dehomogenize_degreeLE hp)
    rwa [siteEvaluation_dehomogenize] at he

end Erdos3.VectorPolynomial

end

end OAI
