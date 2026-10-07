import OAI.Combinatorics.Progressions.Estimates.AllocatedCenteredJointSource
import OAI.Combinatorics.Progressions.Fourier.AllocatedPositiveFourierData
import OAI.Combinatorics.Progressions.Geometry.AllocatedPositiveSpatialComparison

namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel

def physicalDensityProjection.{uK, uJ, uX, uF} {K : Type uK} [Fintype K] {m q : ℕ}
    {J : Fin m → Type uJ} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (root : K → ℤ) (dirs : Fin q → K → ℤ) (d : ℕ)
    (density : CoefficientTorus (K := K) U → ℝ)
    (f : EuclideanJetLayers U (fun j => BoundedBooleanJet (Fin q) (j.val + 1)) → ℝ) : Prop :=
  ∀ {X : Type uX} {F : Type uF} [Fintype F]
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (coeff : F → ℂ) {η : ℝ},
    (∀ z, ‖coefficientTorusFourierSum U frequency coeff z - (density z : ℂ)‖ ≤ η) →
    ∀ (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)),
    (∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j)) →
    ∀ (hm : ∀ j e, coefficients (p j) e ∈ U j) (v : Option K → X → ℝ),
      ‖affineCubeFourierProjection U root dirs frequency p coeff v -
        (f (euclideanCoefficientJetMap U root (Matrix.of dirs)
          (fun j => (Subtype.val : BoundedBooleanJet (Fin q) (j.val + 1) → Finset (Fin q)))
          (affineCoefficientCoverSample U p hm d v)) : ℂ)‖ ≤ η

universe uK uJ uX uF

theorem physicalDensityProjection_sample {K : Type uK} {X : Type uX} {F : Type uF} [Fintype K] [Fintype F] {m q : ℕ}
    {J : Fin m → Type uJ} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (root : K → ℤ) (dirs : Fin q → K → ℤ) (d : ℕ)
    (density : CoefficientTorus (K := K) U → ℝ)
    (f : EuclideanJetLayers U (fun j => BoundedBooleanJet (Fin q) (j.val + 1)) → ℝ)
    (h : physicalDensityProjection.{uK, uJ, uX, uF} U root dirs d density f)
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (coeff : F → ℂ) {η : ℝ}
    (happrox : ∀ z, ‖coefficientTorusFourierSum U frequency coeff z - (density z : ℂ)‖ ≤ η)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j) (base : X → ℤ) (z : Option K × X → ℤ) :
    ‖affineCubeFourierProjection U root dirs frequency
        (fun j => translate (fun i => (base i : ℝ)) (p j)) coeff (fun k i => (z (k,i) : ℝ)) -
      (f (physicalCubeEuclideanSample U d p hm (physicalCubeRootDifferences root (Matrix.of dirs) base z)) : ℂ)‖ ≤ η := by
  rw [← coefficientCoverSample_physicalJet U root dirs d p hp hm base z]
  exact @h X F _ frequency coeff η happrox
    (fun j => translate (fun i => (base i : ℝ)) (p j))
    (fun j => degreeLE_translate (1 : X → ℕ) (fun _ => by norm_num) _ (p j) (hp j))
    (fun j => coefficients_translate_mem (U j) (fun i => (base i : ℝ)) (p j) (hm j))
    (fun k i => (z (k,i) : ℝ))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel MeasureTheory
open scoped BigOperators

theorem exists_allocated_narrow_density_projection (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {G : Type*} [Fintype G] [DecidableEq G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    [DecidableEq (LayerSamplerVariables G I n B)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
    (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox (Fin q) S.value)
    {P W : ℝ} (_hP : 0 ≤ P) (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hW : 0 ≤ W) (_hbudget : allocatedPhysicalRootBudget B U basis S c ≤ W)
    (_hWP : W ≤ Real.exp P) (_hL : (S.value : ℝ) ≤ Real.exp P)
    {M : ℕ} (_hperiod : HasBoundedScalarPeriod (scalarCubeDifferenceMatrix x).mulVecLin.range M)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin q) (allocatedPrincipalSides B U basis S))
    {X : Type*} [Fintype X] [DecidableEq X]
    (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ P)
    {F : Type*} [Fintype F]
    (frequency : F → ∀ j, (LayerSamplerVariables G I n B →₀ ℕ) → J j → ℤ)
    (_hfrequency : ∀ a j d, d.degree ≤ j.val + 1 → ∀ t, |(frequency a j d t : ℝ)| ≤ Real.exp P)
    (coeff : F → ℂ) (_hcoeff : (∑ a, ‖coeff a‖) ≤ Real.exp P)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j) (base : X → ℤ)
    (stride : X → ℕ) (_hs : ∀ d, 0 < stride d) (_hsP : ∀ d, (stride d : ℝ) ≤ Real.exp P)
    {τ ξ ε : ℝ} (_hτ : 0 < τ) (_hτP : τ⁻¹ ≤ Real.exp P)
    (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hξP : ξ⁻¹ ≤ Real.exp P)
    (_hε : 0 < ε) (_hεP : ε⁻¹ ≤ Real.exp P)
    (N : X → ℕ) (_hsize : ∀ d, Real.exp ((P + A) ^ A) ≤ (N d : ℝ))
    {rank : ℝ} (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (p j))
    (_hRank : Real.exp ((P + A) ^ A) ≤ rank)
    (test : Finset (Fin q) → (X → ℝ) → ℂ) (_htest : ∀ s v, ‖test s v‖ ≤ 1)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty)
    (density : CoefficientTorus (K := LayerSamplerVariables G I n B) U → ℝ)
    (D : ℕ) (f : EuclideanJetLayers U (fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)) → ℝ)
    {η : ℝ} (_hη : 0 ≤ η)
    (_happrox : ∀ v, ‖(density v : ℂ) - coefficientTorusFourierSum U frequency coeff v‖ ≤ η)
    {Z : ℝ} (_hZnorm : 0 < Z),
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let root := allocatedPhysicalCubeRoot B U basis S c x y
    let dirs := allocatedPhysicalCubeDirections B U basis S x y
    let pa := fun j => translate (fun d => (base d : ℝ)) (p j)
    let hma := fun j => coefficients_translate_mem (U j) (fun d => (base d : ℝ)) (p j) (hm j)
    ∀ (_hpositive : ∀ z : Option (LayerSamplerVariables G I n B) × X → ℤ,
      ‖affineCubeFourierProjection U root dirs frequency pa coeff (fun k d => (z (k, d) : ℝ)) -
        (f (euclideanCoefficientJetMap U root dirs
          (fun j => (Subtype.val : BoundedBooleanJet (Fin q) (j.val + 1) → Finset (Fin q)))
          (affineCoefficientCoverSample U pa hma D (fun k d => (z (k, d) : ℝ)))) : ℂ)‖ ≤ η),
    ∃ (hV : ∀ z, 0 < V z) (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T V z),
      ‖(∑' z, ((selectedResidueSmoothPMF stride T V hV hZ z).toReal : ℂ) *
        (physicalCubeSiteTest test (physicalCubeRootDifferences root dirs base z) *
          (density (affineSampleCoefficientTorus U pa hma (fun k d => (z (k, d) : ℝ))) : ℂ))) / (Z : ℂ) -
        (∑' z, ((selectedResidueSmoothPMF stride T V hV hZ z).toReal : ℂ) *
          physicalCubePositiveTest U D p hm f test (physicalCubeRootDifferences root dirs base z)) /
          (Z : ℂ)‖ ≤ (2 * η + ε) / Z := by
  obtain ⟨A₀, _, hprojection⟩ := exists_affine_cube_fourier_projection m q
  obtain ⟨A, hA, hbudget⟩ := exists_natPolynomial_eval_budget
    ((8 * Polynomial.X + Polynomial.C (q + 130 + A₀)) ^ A₀)
  refine ⟨A, hA, ?_⟩
  intro G _ _ I _ n B _ _ J _ U basis R σ S c x P W hP hK hW hroot hWP hL M hperiod y
    X _ _ hX hdim F _ frequency hfrequency coeff hcoeff p hp hm base stride hs hsP
    τ ξ ε hτ hτP hξ hξ1 hξP hε hεP N hsize rank hrank hRank test htest T hT density D f η hη happrox Z hZnorm
    V root dirs pa hma hpositive
  let Q := spatialSamplingBudget (2 * P) + (q + 2 : ℕ)
  have hP2 : 0 ≤ 2 * P := by positivity
  have hPQ : P ≤ Q := by dsimp [Q, spatialSamplingBudget]; linarith [Nat.cast_nonneg (α := ℝ) (q + 2)]
  have hQ : 0 ≤ Q := hP.trans hPQ
  have hsiteQ : P + (q + 2 : ℕ) ≤ Q := by dsimp [Q, spatialSamplingBudget]; linarith
  have heval : Q + A₀ = 8 * P + (q + 130 + A₀ : ℕ) := by
    dsimp [Q, spatialSamplingBudget]
    push_cast
    ring
  have hcost : (Q + A₀) ^ A₀ ≤ (P + A) ^ A := by
    rw [heval]
    simpa [Polynomial.eval₂_pow] using hbudget P hP
  have hExp := Real.exp_le_exp.mpr hPQ
  obtain ⟨a, ha, _, hperiod⟩ := hperiod
  have hlin : LinearIndependent ℝ (fun i k => (dirs i k : ℝ)) :=
    linearIndependent_of_fixed_kernel_period (scalarCubeDifferenceMatrix x) dirs Sum.inl
      (fun _ _ => rfl) (by exact_mod_cast ha.ne') hperiod
  have hpa (j) : DegreeLE (1 : X → ℕ) (j.val + 1) (pa j) :=
    degreeLE_translate (1 : X → ℕ) (fun _ => by norm_num) _ (p j) (hp j)
  have hra (j) : HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (pa j) :=
    (hasLayerSamplingRank_translate_iff (fun d => (base d : ℝ)) (j.val + 1)
      (fun d => (N d : ℝ)) rank (U j) (p j) (hp j)).mpr (hrank j)
  have hN (d) : 0 < N d := by exact_mod_cast (Real.exp_pos _).trans_le (hsize d)
  have hV : ∀ z, 0 < V z := narrowTrimmedSpatialWidths_pos hW hτ hξ N hN
  have hξτ : 0 < ξ * τ := mul_pos hξ hτ
  have hξτP : (ξ * τ)⁻¹ ≤ Real.exp (2 * P) := by
    rw [mul_inv_rev]
    calc
      _ ≤ Real.exp P * Real.exp P := mul_le_mul hτP hξP (inv_nonneg.mpr hξ.le) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add, ← two_mul]
  have hρP : 1 / spatialWidthFraction (2 * P) (ξ * τ) ≤ Real.exp Q :=
    (spatialWidthFraction_inv_le hP2 hξτ hξτP).trans
      (Real.exp_le_exp.mpr (le_add_of_nonneg_right (Nat.cast_nonneg _)))
  have hwidth (z) : spatialWidthFraction (2 * P) (ξ * τ) * (N z.2 : ℝ) ≤ V z :=
    (spatialWidthFraction_le_allocated_width hP2 hW
      (hWP.trans (Real.exp_le_exp.mpr (by linarith))) hξτ.le N z).trans
        (narrowTrimmedSpatialWidths_lower hW hτ hξ1 N hN z)
  obtain ⟨hZ, hraw⟩ := hprojection hQ (hX.trans hPQ) (hdim.trans hPQ) U root dirs hlin
    (Real.exp_nonneg Q) (Real.exp_nonneg Q) le_rfl le_rfl
    (fun s k => (allocatedPhysicalCube_site_le_exp B U basis S c x y (hroot.trans hWP) hL s k).trans
      (Real.exp_le_exp.mpr hsiteQ)) frequency (fun a j d hd t => (hfrequency a j d hd t).trans hExp)
    coeff (Real.exp_nonneg Q) le_rfl (hcoeff.trans hExp) pa hpa hma stride hs
    (Real.exp_nonneg Q) le_rfl (spatialWidthFraction_pos (2 * P) hξτ) hε hρP
    (by simpa only [one_div] using hεP.trans hExp) (fun d => (hsP d).trans hExp)
    (fun d => (N d : ℝ)) (fun d => (Real.exp_le_exp.mpr hcost).trans (hsize d)) hra
    ((Real.exp_le_exp.mpr hcost).trans hRank) 0 (by simp)
    (fun s u => test s ((fun d => (base d : ℝ)) + u)) (fun s u => htest s _)
    T hT V hV hwidth
  have hweight (z : Option (LayerSamplerVariables G I n B) × X → ℤ) :
      layeredSiteWeight 0 (fun s => affineSite root dirs s)
        (fun s u => test s ((fun d => (base d : ℝ)) + u)) (fun k d => (z (k, d) : ℝ)) =
        physicalCubeSiteTest test (physicalCubeRootDifferences root dirs base z) :=
    layeredSiteWeight_physicalCube root dirs base test z
  have hdirs : Matrix.of dirs = dirs := rfl
  have hfirst := selectedResidue_positive_density_projection_error U root dirs D p hp hm
    frequency coeff test htest base stride T V hV hZ density f hη happrox hpositive
    (by simpa only [hweight, hdirs, pa] using hraw)
  refine ⟨hV, hZ, ?_⟩
  rw [← sub_div, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hZnorm]
  exact div_le_div_of_nonneg_right hfirst hZnorm.le

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel MeasureTheory
open scoped BigOperators Classical

universe uX uF

theorem exists_allocated_mixture_density_projection (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {G : Type*} [Fintype G] [DecidableEq G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
    [DecidableEq (LayerSamplerVariables G I n B)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
    (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox (Fin q) S.value)
    {P W : ℝ} (_hP : 0 ≤ P) (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hW : 0 ≤ W) (_hbudget : allocatedPhysicalRootBudget B U basis S c ≤ W)
    (_hWP : W ≤ Real.exp P) (_hL : (S.value : ℝ) ≤ Real.exp P)
    {M : ℕ} (_hperiod : HasBoundedScalarPeriod (scalarCubeDifferenceMatrix x).mulVecLin.range M)
    {X : Type uX} [Fintype X] [DecidableEq X]
    (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ P)
    {F : Type uF} [Fintype F]
    (frequency : F → ∀ j, (LayerSamplerVariables G I n B →₀ ℕ) → J j → ℤ)
    (_hfrequency : ∀ a j d, d.degree ≤ j.val + 1 → ∀ t, |(frequency a j d t : ℝ)| ≤ Real.exp P)
    (coeff : F → ℂ) (_hcoeff : (∑ a, ‖coeff a‖) ≤ Real.exp P)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j) (base : X → ℤ)
    (stride : X → ℕ) (_hs : ∀ d, 0 < stride d) (_hsP : ∀ d, (stride d : ℝ) ≤ Real.exp P)
    {τ ξ ε : ℝ} (_hτ : 0 < τ) (_hτP : τ⁻¹ ≤ Real.exp P)
    (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hξP : ξ⁻¹ ≤ Real.exp P)
    (_hε : 0 < ε) (_hεP : ε⁻¹ ≤ Real.exp P)
    (N : X → ℕ) (_hsize : ∀ d, Real.exp ((P + A) ^ A) ≤ (N d : ℝ))
    {rank : ℝ} (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (p j))
    (_hRank : Real.exp ((P + A) ^ A) ≤ rank)
    (test : Finset (Fin q) → (X → ℝ) → ℂ) (_htest : ∀ s v, ‖test s v‖ ≤ 1)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty)
    (density : CoefficientTorus (K := LayerSamplerVariables G I n B) U → ℝ)
    (D : ℕ)
    (f : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin q) (allocatedPrincipalSides B U basis S) →
      EuclideanJetLayers U (fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)) → ℝ)
    (_hproject : ∀ y, physicalDensityProjection.{_, _, uX, uF} U
      (allocatedPhysicalCubeRoot B U basis S c x y)
      (allocatedPhysicalCubeDirections B U basis S x y) D density (f y))
    {η : ℝ} (_hη : 0 ≤ η)
    (_happrox : ∀ v, ‖(density v : ℂ) - coefficientTorusFourierSum U frequency coeff v‖ ≤ η)
    {Z : ℝ} (_hZnorm : 0 < Z),
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    ∀ (hV : ∀ z, 0 < V z) (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride T V z),
    let law := principalTupleWeights (α := Fin q) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)
    let source := fun y => ∑' z,
      ((selectedResidueSmoothPMF stride T V hV hmass z).toReal : ℂ) *
        (physicalCubeSiteTest test (physicalCubeRootDifferences
          (allocatedPhysicalCubeRoot B U basis S c x y)
          (allocatedPhysicalCubeDirections B U basis S x y) base z) *
          (density (affineSampleCoefficientTorus U
            (fun j => translate (fun t => (base t : ℝ)) (p j))
            (fun j => coefficients_translate_mem (U j) (fun t => (base t : ℝ)) (p j) (hm j))
            (fun k t => (z (k, t) : ℝ))) : ℂ))
    let projected := fun y => ∑' z,
      ((selectedResidueSmoothPMF stride T V hV hmass z).toReal : ℂ) *
        physicalCubePositiveTest U D p hm (f y) test (physicalCubeRootDifferences
          (allocatedPhysicalCubeRoot B U basis S c x y)
          (allocatedPhysicalCubeDirections B U basis S x y) base z)
    ‖law.complexMean source / (Z : ℂ) - law.complexMean projected / (Z : ℂ)‖ ≤ (2 * η + ε) / Z := by
  obtain ⟨A, hA, hprojection⟩ := exists_allocated_narrow_density_projection m q
  refine ⟨A, hA, ?_⟩
  intro G _ _ I _ _ n B _ _ _ J _ U basis R σ S c x P W hP hK hW hroot hWP hL M hperiod
    X _ _ hX hdim F _ frequency hfrequency coeff hcoeff p hp hm base stride hs hsP
    τ ξ ε hτ hτP hξ hξ1 hξP hε hεP N hsize rank hrank hRank test htest T hT density D f
    hproject η hη happrox Z hZnorm V hV hmass law source projected
  have hpoint (y) : ‖source y / (Z : ℂ) - projected y / (Z : ℂ)‖ ≤ (2 * η + ε) / Z := by
    obtain ⟨_, _, he⟩ := hprojection B U basis S c x hP hK hW hroot hWP hL hperiod y
      hX hdim frequency hfrequency coeff hcoeff p hp hm base stride hs hsP
      hτ hτP hξ hξ1 hξP hε hεP N hsize hrank hRank test htest T hT density D (f y)
      hη happrox hZnorm
      (fun z => (hproject y) frequency coeff
        (fun v => by rw [norm_sub_rev]; exact happrox v)
        (fun j => translate (fun t => (base t : ℝ)) (p j))
        (fun j => degreeLE_translate (1 : X → ℕ) (fun _ => by norm_num) _ (p j) (hp j))
        (fun j => coefficients_translate_mem (U j) (fun t => (base t : ℝ)) (p j) (hm j))
        (fun k t => (z (k, t) : ℝ)))
    exact he
  have hmean := law.norm_complexMean_sub_le
    (fun y => source y / (Z : ℂ)) (fun y => projected y / (Z : ℂ))
    (fun _ => (2 * η + ε) / Z) (fun y _ => hpoint y)
  rw [law.mean_const] at hmean
  simpa only [FiniteProbabilityWeights.complexMean, mul_div_assoc, Finset.sum_div] using hmean

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel MeasureTheory
open scoped BigOperators Classical

universe uX uF

theorem exists_allocated_mixture_density_projection_law (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {G : Type*} [Fintype G] [DecidableEq G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
    [DecidableEq (LayerSamplerVariables G I n B)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
    (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox (Fin q) S.value)
    {P W : ℝ} (_hP : 0 ≤ P) (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hW : 0 ≤ W) (_hbudget : allocatedPhysicalRootBudget B U basis S c ≤ W)
    (_hWP : W ≤ Real.exp P) (_hL : (S.value : ℝ) ≤ Real.exp P)
    {M : ℕ} (_hperiod : HasBoundedScalarPeriod (scalarCubeDifferenceMatrix x).mulVecLin.range M)
    {X : Type uX} [Fintype X] [DecidableEq X]
    (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ P)
    {F : Type uF} [Fintype F]
    (frequency : F → ∀ j, (LayerSamplerVariables G I n B →₀ ℕ) → J j → ℤ)
    (_hfrequency : ∀ a j d, d.degree ≤ j.val + 1 → ∀ t, |(frequency a j d t : ℝ)| ≤ Real.exp P)
    (coeff : F → ℂ) (_hcoeff : (∑ a, ‖coeff a‖) ≤ Real.exp P)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j) (base : X → ℤ)
    (stride : X → ℕ) (_hs : ∀ d, 0 < stride d) (_hsP : ∀ d, (stride d : ℝ) ≤ Real.exp P)
    {τ ξ ε : ℝ} (_hτ : 0 < τ) (_hτP : τ⁻¹ ≤ Real.exp P)
    (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hξP : ξ⁻¹ ≤ Real.exp P)
    (_hε : 0 < ε) (_hεP : ε⁻¹ ≤ Real.exp P)
    (N : X → ℕ) (_hsize : ∀ d, Real.exp ((P + A) ^ A) ≤ (N d : ℝ))
    {rank : ℝ} (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (p j))
    (_hRank : Real.exp ((P + A) ^ A) ≤ rank)
    (test : Finset (Fin q) → (X → ℝ) → ℂ) (_htest : ∀ s v, ‖test s v‖ ≤ 1)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty)
    (density : CoefficientTorus (K := LayerSamplerVariables G I n B) U → ℝ)
    (D : ℕ)
    (f : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin q) (allocatedPrincipalSides B U basis S) →
      EuclideanJetLayers U (fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)) → ℝ)
    (_hproject : ∀ y, physicalDensityProjection.{_, _, uX, uF} U
      (allocatedPhysicalCubeRoot B U basis S c x y)
      (allocatedPhysicalCubeDirections B U basis S x y) D density (f y))
    {η : ℝ} (_hη : 0 ≤ η)
    (_happrox : ∀ v, ‖(density v : ℂ) - coefficientTorusFourierSum U frequency coeff v‖ ≤ η)
    {Z : ℝ} (_hZnorm : 0 < Z),
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    ∀ (hV : ∀ z, 0 < V z) (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride T V z),
    ∀ law : FiniteProbabilityWeights (PrincipalIntegerTuples B (layerSamplerDegree I n)
      (Fin q) (allocatedPrincipalSides B U basis S)),
    let source := fun y => ∑' z,
      ((selectedResidueSmoothPMF stride T V hV hmass z).toReal : ℂ) *
        (physicalCubeSiteTest test (physicalCubeRootDifferences
          (allocatedPhysicalCubeRoot B U basis S c x y)
          (allocatedPhysicalCubeDirections B U basis S x y) base z) *
          (density (affineSampleCoefficientTorus U
            (fun j => translate (fun t => (base t : ℝ)) (p j))
            (fun j => coefficients_translate_mem (U j) (fun t => (base t : ℝ)) (p j) (hm j))
            (fun k t => (z (k, t) : ℝ))) : ℂ))
    let projected := fun y => ∑' z,
      ((selectedResidueSmoothPMF stride T V hV hmass z).toReal : ℂ) *
        physicalCubePositiveTest U D p hm (f y) test (physicalCubeRootDifferences
          (allocatedPhysicalCubeRoot B U basis S c x y)
          (allocatedPhysicalCubeDirections B U basis S x y) base z)
    ‖law.complexMean source / (Z : ℂ) - law.complexMean projected / (Z : ℂ)‖ ≤ (2 * η + ε) / Z := by
  obtain ⟨A, hA, hprojection⟩ := exists_allocated_narrow_density_projection m q
  refine ⟨A, hA, ?_⟩
  intro G _ _ I _ _ n B _ _ _ J _ U basis R σ S c x P W hP hK hW hroot hWP hL M hperiod
    X _ _ hX hdim F _ frequency hfrequency coeff hcoeff p hp hm base stride hs hsP
    τ ξ ε hτ hτP hξ hξ1 hξP hε hεP N hsize rank hrank hRank test htest T hT density D f
    hproject η hη happrox Z hZnorm V hV hmass law source projected
  have hpoint (y) : ‖source y / (Z : ℂ) - projected y / (Z : ℂ)‖ ≤ (2 * η + ε) / Z := by
    obtain ⟨_, _, he⟩ := hprojection B U basis S c x hP hK hW hroot hWP hL hperiod y
      hX hdim frequency hfrequency coeff hcoeff p hp hm base stride hs hsP
      hτ hτP hξ hξ1 hξP hε hεP N hsize hrank hRank test htest T hT density D (f y)
      hη happrox hZnorm
      (fun z => (hproject y) frequency coeff
        (fun v => by rw [norm_sub_rev]; exact happrox v)
        (fun j => translate (fun t => (base t : ℝ)) (p j))
        (fun j => degreeLE_translate (1 : X → ℕ) (fun _ => by norm_num) _ (p j) (hp j))
        (fun j => coefficients_translate_mem (U j) (fun t => (base t : ℝ)) (p j) (hm j))
        (fun k t => (z (k, t) : ℝ)))
    exact he
  have hmean := law.norm_complexMean_sub_le
    (fun y => source y / (Z : ℂ)) (fun y => projected y / (Z : ℂ))
    (fun _ => (2 * η + ε) / Z) (fun y _ => hpoint y)
  rw [law.mean_const] at hmean
  simpa only [FiniteProbabilityWeights.complexMean, mul_div_assoc, Finset.sum_div] using hmean

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

universe uX

theorem exists_allocated_original_density_projection (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {G : Type*} [Fintype G] [DecidableEq G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
    [DecidableEq (LayerSamplerVariables G I n B)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
    (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox (Fin q) S.value)
    (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ V j)
    (_hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    {P W : ℝ} (_hP : 0 ≤ P) (_hm : (m : ℝ) ≤ P)
    (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hW : 0 ≤ W) (_hbudget : allocatedPhysicalRootBudget B U basis S c ≤ W)
    (_hWP : W ≤ Real.exp P) (_hL : (S.value : ℝ) ≤ Real.exp P)
    (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (_hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    {M : ℕ} (_hperiod : HasBoundedScalarPeriod (scalarCubeDifferenceMatrix x).mulVecLin.range M)
    {X : Type uX} [Fintype X] [DecidableEq X]
    (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ P)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j) (base : X → ℤ)
    (stride : X → ℕ) (_hs : ∀ d, 0 < stride d) (_hsP : ∀ d, (stride d : ℝ) ≤ Real.exp P)
    {τ ξ : ℝ} (_hτ : 0 < τ) (_hτP : τ⁻¹ ≤ Real.exp P)
    (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hξP : ξ⁻¹ ≤ Real.exp P)
    (N : X → ℕ) (_hsize : ∀ d, Real.exp ((P + A) ^ A) ≤ (N d : ℝ))
    {rank : ℝ} (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (p j))
    (_hRank : Real.exp ((P + A) ^ A) ≤ rank)
    (test : Finset (Fin q) → (X → ℝ) → ℂ) (_htest : ∀ s v, ‖test s v‖ ≤ 1)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty)
    (D : ℕ)
    (f : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin q) (allocatedPrincipalSides B U basis S) →
      EuclideanJetLayers U (fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)) → ℝ),
    let density := allocatedCoefficientDensity B U basis hb o hR hσ S
    ∀ (_hproject : ∀ y, physicalDensityProjection.{_, _, uX, 0} U
      (allocatedPhysicalCubeRoot B U basis S c x y)
      (allocatedPhysicalCubeDirections B U basis S x y) D density (f y))
    {Z : ℝ} (_hZ : 0 < Z) (_hZi : Z⁻¹ ≤ Real.exp P),
    let widths := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    ∀ (hwidths : ∀ z, 0 < widths z) (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride T widths z),
    let law := principalTupleWeights (α := Fin q) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)
    let source := fun y => ∑' z,
      ((selectedResidueSmoothPMF stride T widths hwidths hmass z).toReal : ℂ) *
        (physicalCubeSiteTest test (physicalCubeRootDifferences
          (allocatedPhysicalCubeRoot B U basis S c x y)
          (allocatedPhysicalCubeDirections B U basis S x y) base z) *
          (density (affineSampleCoefficientTorus U
            (fun j => translate (fun t => (base t : ℝ)) (p j))
            (fun j => coefficients_translate_mem (U j) (fun t => (base t : ℝ)) (p j) (hm j))
            (fun k t => (z (k, t) : ℝ))) : ℂ))
    let projected := fun y => ∑' z,
      ((selectedResidueSmoothPMF stride T widths hwidths hmass z).toReal : ℂ) *
        physicalCubePositiveTest U D p hm (f y) test (physicalCubeRootDifferences
          (allocatedPhysicalCubeRoot B U basis S c x y)
          (allocatedPhysicalCubeDirections B U basis S x y) base z)
    ‖law.complexMean source / (Z : ℂ) - law.complexMean projected / (Z : ℂ)‖ ≤ Real.exp (-P) := by
  obtain ⟨A₀, _, hprojection⟩ := exists_allocated_mixture_density_projection m q
  obtain ⟨b, _, hbnd⟩ := exists_positiveComparisonDataBudget_bound m q
  obtain ⟨A, hA, hbudget⟩ := exists_natPolynomial_eval_budget
    (((Polynomial.X + Polynomial.C b) ^ b + Polynomial.C A₀) ^ A₀)
  refine ⟨A, hA, ?_⟩
  intro G _ _ I _ _ n B _ _ _ J _ U basis R σ S c x hb o hR hσ C V hC hV
    hσ1 Cinv hCinv hchart hsmall P W hP hmSize hK hW hroot hWP hL hRP hσP hcount hI hn hJ
    hAP hCP hVP M hperiod X _ _ hX hdim p hp hm base stride hs hsP τ ξ hτ hτP hξ hξ1 hξP
    N hsize rank hrank hRank test htest T hT D f density hproject Z hZ hZi widths hwidths hmass
    law source projected
  let Q := positiveComparisonDataBudget m q P
  obtain ⟨hQ, hPQ, haccQ, _, _⟩ := positiveComparisonDataBudget_bounds m q hP
  have hExp := Real.exp_le_exp.mpr hPQ
  have hcut : (Q + A₀) ^ A₀ ≤ (P + A) ^ A := by
    calc
      _ ≤ ((P + b) ^ b + A₀) ^ A₀ :=
        pow_le_pow_left₀ (add_nonneg hQ (Nat.cast_nonneg A₀))
          (add_le_add (hbnd P hP) le_rfl) A₀
      _ ≤ _ := by simpa [Polynomial.eval₂_pow] using hbudget P hP
  obtain ⟨_, F, inst, frequency, coeff, hfreq, hcoeff, happ⟩ :=
    exists_allocated_positive_fourier_data B U basis hb o S C V hC hV q
      hR hσ hσ1 Cinv hCinv hchart hsmall hP hmSize hK hRP hσP hcount hI hn hJ hAP hL hCP hVP
  let _ := inst
  have hη : 0 < positiveProjectionAccuracy P := Real.exp_pos _
  have hηQ : (positiveProjectionAccuracy P)⁻¹ ≤ Real.exp Q := by
    simp only [positiveProjectionAccuracy, Real.exp_neg, inv_inv]
    exact Real.exp_le_exp.mpr haccQ
  have he := hprojection B U basis S c x hQ (hK.trans hPQ) hW hroot
    (hWP.trans hExp) (hL.trans hExp) hperiod (hX.trans hPQ) (hdim.trans hPQ)
    frequency hfreq coeff hcoeff p hp hm base stride hs (fun t => (hsP t).trans hExp)
    hτ (hτP.trans hExp) hξ hξ1 (hξP.trans hExp) hη hηQ N
    (fun t => (Real.exp_le_exp.mpr hcut).trans (hsize t)) hrank
    ((Real.exp_le_exp.mpr hcut).trans hRank) test htest T hT density D f hproject hη.le happ hZ
    hwidths hmass
  apply he.trans
  calc
    (2 * positiveProjectionAccuracy P + positiveProjectionAccuracy P) / Z =
        3 * positiveProjectionAccuracy P * Z⁻¹ := by ring
    _ ≤ 3 * positiveProjectionAccuracy P * Real.exp P :=
      mul_le_mul_of_nonneg_left hZi (by positivity)
    _ = 3 * Real.exp (-(P + 4)) := by
      rw [mul_assoc, positiveProjectionAccuracy, ← Real.exp_add]
      congr 2
      ring
    _ ≤ Real.exp 4 * Real.exp (-(P + 4)) :=
      mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (4 : ℝ)]) (Real.exp_nonneg _)
    _ = Real.exp (-P) := by rw [← Real.exp_add]; congr 1; ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

universe uX

variable {m dim : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))) (d : ℕ)
variable (g : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S) →
  EuclideanJetLayers U (fun j => BoundedBooleanJet (Fin dim) (j.val + 1)) → ℝ)

def AllocatedOriginalSourceProjectionAt (P : ℝ) (K : ℕ) : Prop :=
  ∀ {Q : ℝ}, P ≤ Q → 1 ≤ Q →
  ∀ {X : Type uX} [Fintype X] [DecidableEq X],
  (Fintype.card X : ℝ) ≤ Q →
  (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ Q →
  ∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)),
  (∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j)) →
  ∀ (hmem : ∀ j e, coefficients (poly j) e ∈ U j) (base : X → ℤ)
    (stride : X → ℕ), (∀ t, 0 < stride t) → (∀ t, (stride t : ℝ) ≤ Real.exp Q) →
  ∀ {W τ ξ : ℝ} (hW : 0 ≤ W),
  allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W → W ≤ Real.exp Q →
  ∀ (hτ : 0 < τ), τ⁻¹ ≤ Real.exp Q →
  ∀ (hξ : 0 < ξ), ξ ≤ 1 → ξ⁻¹ ≤ Real.exp Q →
  ∀ (N : X → ℕ) (hN : ∀ t, 0 < N t),
  (∀ t, Real.exp ((Q + K) ^ K) ≤ (N t : ℝ)) →
  ∀ {rank : ℝ},
  (∀ j, HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) rank (U j) (poly j)) →
  Real.exp ((Q + K) ^ K) ≤ rank →
  ∀ (test : Finset (Fin dim) → (X → ℝ) → ℂ), (∀ s v, ‖test s v‖ ≤ 1) →
  ∀ (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)),
  cells.Nonempty → ∀ {Z : ℝ}, 1 / 2 ≤ Z →
  ∀ (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells
    (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z),
  ‖allocatedOriginalTupleSource B U b hR hσ S x X stride hb o N hN hW hτ hξ base cells hmass
      (physicalCubeSiteTest test) Z poly hmem -
    allocatedProjectedTupleSource B U b S x X stride g N hN hW hτ hξ base cells hmass
      (physicalCubeEuclideanSample U d poly hmem) (physicalCubeSiteTest test) Z‖ ≤ Real.exp (-Q)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

universe uX

theorem exists_allocated_original_source_projection (m dim : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {G : Type*} [Fintype G] [DecidableEq G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
    [DecidableEq (LayerSamplerVariables G I n B)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
    (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ V j)
    (_hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    {P : ℝ} (_hP : 0 ≤ P) (_hm : (m : ℝ) ≤ P)
    (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hL : (S.value : ℝ) ≤ Real.exp P)
    (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (_hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    {M : ℕ} (_hperiod : HasBoundedScalarPeriod (scalarCubeDifferenceMatrix x).mulVecLin.range M)
    (d : ℕ)
    (g : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U basis S) →
      EuclideanJetLayers U (fun j => BoundedBooleanJet (Fin dim) (j.val + 1)) → ℝ)
    (_hproject : ∀ y, physicalDensityProjection.{_, _, uX, 0} U
      (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
      (allocatedPhysicalCubeDirections B U basis S x y) d
      (allocatedCoefficientDensity B U basis hb o hR hσ S) (g y)),
    AllocatedOriginalSourceProjectionAt.{uX} B U basis hR hσ S x hb o d g P A := by
  obtain ⟨A, hA, hprojection⟩ := exists_allocated_original_density_projection m dim
  refine ⟨A, hA, ?_⟩
  intro G _ _ I _ _ n B _ _ _ J _ U b R σ S x hb o hR hσ C V hC hV
    hσ1 Cinv hCinv hchart hsmall P hP hm hK hL hRP hσP hcount hI hn hJ hAP hCP hVP
    M hperiod d g hproject
  unfold AllocatedOriginalSourceProjectionAt
  intro Q hPQ hQ1 X _ _ hX hdim poly hpoly hmem base stride hs hsQ W τ ξ hW hbudget hWQ
    hτ hτQ hξ hξ1 hξQ N hN hsize rank hrank hRank test htest cells hcells Z hZ hmass
  have hQ : 0 ≤ Q := hP.trans hPQ
  have hExp := Real.exp_le_exp.mpr hPQ
  have hZpos : 0 < Z := by linarith
  have hZi : Z⁻¹ ≤ Real.exp Q := by
    have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hZ
    have hi' : Z⁻¹ ≤ (2 : ℝ) := by simpa only [one_div, inv_inv] using hi
    exact hi'.trans (by linarith [Real.add_one_le_exp Q])
  have h := hprojection B U b S (fun _ => 0) x hb o hR hσ C V hC hV hσ1 Cinv hCinv hchart
    hsmall hQ (hm.trans hPQ) (hK.trans hPQ) hW hbudget hWQ (hL.trans hExp)
    (fun j => (hRP j).trans hExp) (fun j => (hσP j).trans hExp)
    (fun j => (hcount j).trans hPQ) (fun j => (hI j).trans hPQ)
    (fun j => (hn j).trans hPQ) (fun j => (hJ j).trans hPQ) (hAP.trans hExp)
    (fun j => (hCP j).trans hExp) (fun j => (hVP j).trans hExp) hperiod hX hdim
    poly hpoly hmem base stride hs hsQ hτ hτQ hξ hξ1 hξQ N hsize hrank hRank
    test htest cells hcells d g hproject hZpos hZi
    (narrowTrimmedSpatialWidths_pos hW hτ hξ N hN) hmass
  simpa only [allocatedOriginalTupleSource, allocatedProjectedTupleSource, physicalCubePositiveTest] using h

end Erdos3.VectorPolynomial

end

end OAI
