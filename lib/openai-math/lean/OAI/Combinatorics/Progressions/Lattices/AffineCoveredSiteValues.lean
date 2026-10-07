import OAI.Combinatorics.Progressions.Geometry.GeometricRetainedCommonCover

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators

noncomputable def affineCoveredSiteSample {I K : Type*} [Fintype K] {m q : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (root : K → ℤ) (difference : Fin q → K → ℤ) (D : ℕ)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hm : ∀ j d, coefficients (p j) d ∈ U j) (x : Option K → I → ℝ) :
    ∀ j, SubspaceArrayTorus (Finset (Fin q)) (U j) := fun j =>
  QuotientAddGroup.mk' (subspaceArrayIntegerLattice (Finset (Fin q)) (U j))
    ((D : ℝ)⁻¹ • VectorPolynomial.siteEvaluation
      (fun s k => ((affineSite root difference s (some k) : ℤ) : ℝ))
      (substitute (affineParameterSubstitution x) (restrictCoefficients (U j) (p j) (hm j))))

theorem layeredCoefficientCharacter_of_site_factorization
    {I K : Type*} [Fintype K] {m q : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (difference : Fin q → K → ℤ)
    (D : ℕ) (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (b : ∀ j, Matrix (Finset (Fin q)) (J j) ℤ)
    (hchar : ∀ (j : Fin m) (v : VectorPolynomial K ℝ (U j)),
      DegreeLE (1 : K → ℕ) (j.val + 1) v →
      CircleFourier.character
        (coefficientFunctional (fun d a => (frequency j d a : ℝ))
          (map (U j).subtype v) : CircleFourier.Circle) =
      subspaceArrayCharacter (U j) (b j)
        (QuotientAddGroup.mk' (subspaceArrayIntegerLattice (Finset (Fin q)) (U j))
          ((D : ℝ)⁻¹ • VectorPolynomial.siteEvaluation
            (fun s k => ((affineSite root difference s (some k) : ℤ) : ℝ)) v)))
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j) (x : Option K → I → ℝ) :
    layeredCoefficientCharacter
      (fun j => affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ)))) p x =
      ∏ j, subspaceArrayCharacter (U j) (b j)
        (affineCoveredSiteSample U root difference D p hm x j) := by
  unfold layeredCoefficientCharacter
  rw [character_real_sum]
  apply Finset.prod_congr rfl
  intro j _
  rw [affineModeLift_substitute]
  have he := hchar j
    (substitute (affineParameterSubstitution x) (restrictCoefficients (U j) (p j) (hm j)))
    (degreeLE_substitute_affine _ (affineParameterSubstitution_degree x) _
      (degreeLE_restrictCoefficients (U j) (p j) (hm j) (hp j)))
  simpa only [map_substitute, map_restrictCoefficients, affineCoveredSiteSample] using he

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators

theorem affine_site_substitution_eval {I K W : Type*} [Fintype K]
    [AddCommGroup W] [Module ℝ W] {q : ℕ}
    (root : K → ℤ) (difference : Fin q → K → ℤ)
    (p : VectorPolynomial I ℝ W) (x : Option K → I → ℝ) :
    VectorPolynomial.siteEvaluation
      (fun s k => ((affineSite root difference s (some k) : ℤ) : ℝ))
      (substitute (affineParameterSubstitution x) p) =
      fun s => eval (integerSiteValue (affineSite root difference s) x) p := by
  funext s
  change eval _ (substitute _ p) = _
  rw [eval_substitute]
  apply congrArg (fun t : I → ℝ => eval t p)
  funext i
  rw [affineParameterSubstitution_eval]
  simp [integerSiteValue, Fintype.sum_option, affineSite, Finset.sum_apply,
    zsmul_eq_mul, mul_comm]

theorem affineCoveredSiteSample_eq_values {I K : Type*} [Fintype K] {m q : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (root : K → ℤ) (difference : Fin q → K → ℤ) (D : ℕ)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hm : ∀ j d, coefficients (p j) d ∈ U j) (x : Option K → I → ℝ) (j : Fin m) :
    affineCoveredSiteSample U root difference D p hm x j =
      QuotientAddGroup.mk' (subspaceArrayIntegerLattice (Finset (Fin q)) (U j))
        ((D : ℝ)⁻¹ • fun s => eval (integerSiteValue (affineSite root difference s) x)
          (restrictCoefficients (U j) (p j) (hm j))) := by
  unfold affineCoveredSiteSample
  rw [affine_site_substitution_eval]

end Erdos3.BooleanCubeKernel

end

end OAI
