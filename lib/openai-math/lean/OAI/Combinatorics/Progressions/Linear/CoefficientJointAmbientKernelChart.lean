import OAI.Combinatorics.Progressions.Fourier.StandardJetFourier

namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped BigOperators NNReal

variable {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

omit [Fintype K] in
theorem coefficientAmbientTorus_canonicalSample (x : CoefficientSamplerArrays (K := K) I n) :
    coefficientAmbientTorus U (canonicalCoefficientSample U b hb o x) =
      fun a => (coefficientSamplerAmbientPoint U b o x a : UnitAddCircle) := by
  funext a
  rcases a with ⟨⟨j, e⟩, i⟩
  have he : coefficientCoordinateTorus U (canonicalCoefficientSample U b hb o x) ⟨j, e⟩ =
      euclideanSubspaceTorusEquiv (U j)
        (mixedArrayQuotient (euclideanSubspace (U j)) (b j) (hb j) (o j) (x j) e) := by
    apply (euclideanSubspaceTorusEquiv (U j)).symm.injective
    rw [← euclideanCoefficientEquiv_apply, canonicalCoefficientSample,
      AddEquiv.apply_symm_apply, AddEquiv.symm_apply_apply]
  change subspaceAmbientTorus (U j)
    (coefficientCoordinateTorus U (canonicalCoefficientSample U b hb o x) ⟨j, e⟩) i = _
  rw [he]
  exact euclideanAmbientTorus_normalized (U j) (b j) (hb j)
    (orthonormalMixedChart (o j)
      (mixedArrayRegroup (I j) (Fin (n j)) (BoundedCoefficientExponent K (j.val + 1)) (x j) e)) i

variable (c w : ∀ j : Fin m, I j → BoundedCoefficientExponent K (j.val + 1) → ℝ)
variable (f : ∀ j : Fin m, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → ℝ → ℝ)
variable (p : ∀ j : Fin m, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → PMF ℤ)

theorem coefficientJointAmbientKernel_chart
    (hf : ∀ j i d (k : ℤ), f j i d ((k : ℝ) / basisAxisScale (b j) i) =
      basisAxisScale (b j) i * (p j i d k).toReal)
    (hs : ∀ j d x, mixedCoefficientDensity (fun i => c j i d) (fun i => w j i d)
      (fun i => p j i d) x ≠ 0 → ∀ a,
        |normalizedLatticePoint (euclideanSubspace (U j)) (b j) (orthonormalMixedChart (o j) x) a| ≤ 1/4)
    (x : CoefficientSamplerArrays (K := K) I n)
    (hx : ∀ a, |coefficientSamplerAmbientPoint U b o x a| < 1/2) :
    coefficientJointAmbientKernel U b o c w f (coefficientSamplerAmbientPoint U b o x) =
      canonicalCoefficientDensity U b hb o c w p (canonicalCoefficientSample U b hb o x) := by
  rw [← coefficientJointAmbientKernel_canonical U b o c w f hb p hf hs,
    coefficientAmbientTorus_canonicalSample]
  exact (smallBoxTorusKernel_local _ (coefficientJointAmbientKernel_support U b o c w f) _ hx).symm

end Erdos3.VectorPolynomial

end

end OAI
