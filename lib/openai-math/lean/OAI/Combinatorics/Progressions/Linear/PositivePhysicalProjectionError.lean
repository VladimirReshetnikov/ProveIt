import OAI.Combinatorics.Progressions.Estimates.PhysicalRowsSiteReconstruction

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

variable {I K F : Type*} [Fintype I] [Fintype K] [Fintype F] {m q : ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (root : K → ℤ) (difference : Fin q → K → ℤ) (D : ℕ)
variable (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
variable (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
variable (hm : ∀ j d, coefficients (p j) d ∈ U j)
variable (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (c : F → ℂ)
variable (test : Finset (Fin q) → (I → ℝ) → ℂ) (htest : ∀ s v, ‖test s v‖ ≤ 1)
variable (base : I → ℤ) (modulus : I → ℕ)
variable (T : Finset (ColumnResiduePattern (Option K) I modulus))
variable (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z)
variable (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T V z)

local notation "frame" => (fun z : Option K × I → ℤ => fun k i => (z (k, i) : ℝ))
local notation "output" => physicalCubeRootDifferences root (Matrix.of difference) base
local notation "law" => selectedResidueSmoothPMF modulus T V hV hZ

include hp htest in
theorem selectedResidue_positive_density_projection_error
    (density : CoefficientTorus (K := K) U → ℝ)
    (f : EuclideanJetLayers U (fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)) → ℝ)
    {η δ : ℝ} (hη : 0 ≤ η)
    (happrox : ∀ x, ‖(density x : ℂ) - coefficientTorusFourierSum U frequency c x‖ ≤ η) :
    let pa := fun j => translate (fun i => (base i : ℝ)) (p j)
    let hma := fun j => coefficients_translate_mem (U j) (fun i => (base i : ℝ)) (p j) (hm j)
    ∀ (_hpositive : ∀ z, ‖affineCubeFourierProjection U root difference frequency pa c (frame z) -
      (f (euclideanCoefficientJetMap U root (Matrix.of difference)
        (fun j => (Subtype.val : BoundedBooleanJet (Fin q) (j.val + 1) → Finset (Fin q)))
        (affineCoefficientCoverSample U pa hma D (frame z))) : ℂ)‖ ≤ η)
    (_hprojection :
      ‖(∑' z, ((law z).toReal : ℂ) * (physicalCubeSiteTest test (output z) *
        affineCubeFourierSum frequency pa c (frame z))) -
        ∑' z, ((law z).toReal : ℂ) * (physicalCubeSiteTest test (output z) *
          affineCubeFourierProjection U root difference frequency pa c (frame z))‖ ≤ δ),
    ‖(∑' z, ((law z).toReal : ℂ) * (physicalCubeSiteTest test (output z) *
      (density (affineSampleCoefficientTorus U pa hma (frame z)) : ℂ))) -
      ∑' z, ((law z).toReal : ℂ) * physicalCubePositiveTest U D p hm f test (output z)‖ ≤ 2 * η + δ := by
  intro pa hma hpositive hprojection
  have hpa (j) : DegreeLE (1 : I → ℕ) (j.val + 1) (pa j) :=
    degreeLE_translate (1 : I → ℕ) (fun _ => by norm_num) _ (p j) (hp j)
  have happ (z) : ‖(density (affineSampleCoefficientTorus U pa hma (frame z)) : ℂ) -
      affineCubeFourierSum frequency pa c (frame z)‖ ≤ η := by
    have h := happrox (affineSampleCoefficientTorus U pa hma (frame z))
    rw [coefficientTorusFourierSum_sample U frequency c pa hpa hma (frame z)] at h
    exact h
  have hpos (z) : ‖affineCubeFourierProjection U root difference frequency pa c (frame z) -
      (f (physicalCubeEuclideanSample U D p hm (output z)) : ℂ)‖ ≤ η := by
    have h := hpositive z
    rw [coefficientCoverSample_physicalJet U root difference D p hp hm base z] at h
    exact h
  exact selectedResidueSmoothPMF_projection_approximation modulus T V hV hZ
    (fun z => physicalCubeSiteTest test (output z))
    (fun z => (density (affineSampleCoefficientTorus U pa hma (frame z)) : ℂ))
    (fun z => affineCubeFourierSum frequency pa c (frame z))
    (fun z => affineCubeFourierProjection U root difference frequency pa c (frame z))
    (fun z => (f (physicalCubeEuclideanSample U D p hm (output z)) : ℂ))
    hη (fun z _ => physicalCubeSiteTest_norm_le test htest (output z))
    (fun z _ => happ z) (fun z _ => hpos z) hprojection

end Erdos3.BooleanCubeKernel

end

end OAI
