import OAI.Combinatorics.Progressions.Linear.AllocatedOriginalSourceProjection

namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel MeasureTheory
open scoped BigOperators Classical NNReal

universe uX

theorem exists_allocated_uniform_mixture_projection (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {G : Type*} [Fintype G] [DecidableEq G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
    [DecidableEq (LayerSamplerVariables G I n B)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
    (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox (Fin q) S.value)
    (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (C Vcap : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ Vcap j)
    (_hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    {P W : ℝ} (_hP : 0 ≤ P) (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hW : 0 ≤ W) (_hbudget : allocatedPhysicalRootBudget B U basis S c ≤ W)
    (_hWP : W ≤ Real.exp P) (_hL : (S.value : ℝ) ≤ Real.exp P)
    (_hm : (m : ℝ) ≤ P)
    (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (_hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (Vcap j : ℝ) ≤ Real.exp P)
    {M : ℕ} (_hperiod : HasBoundedScalarPeriod (scalarCubeDifferenceMatrix x).mulVecLin.range M)
    {X : Type uX} [Fintype X] [DecidableEq X]
    (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ P)
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
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty),
    let density := allocatedCoefficientDensity B U basis hb o hR hσ S
    ∀ (D : ℕ)
    (f : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin q) (allocatedPrincipalSides B U basis S) →
      EuclideanJetLayers U (fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)) → ℝ)
    (_hproject : ∀ y, physicalDensityProjection.{_, _, uX, 0} U
      (allocatedPhysicalCubeRoot B U basis S c x y)
      (allocatedPhysicalCubeDirections B U basis S x y) D density (f y))
    {η : ℝ} (_hη : 0 < η) (_hηP : η⁻¹ ≤ Real.exp P)
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
  obtain ⟨A₀, _, hprojection⟩ := exists_allocated_mixture_density_projection m q
  obtain ⟨b, _, hfourierBound⟩ := exists_allocatedFourierOutputBudget_bound m
  obtain ⟨A, hA, hbudget⟩ := exists_natPolynomial_eval_budget
    (((Polynomial.X + Polynomial.C b) ^ b + Polynomial.X + Polynomial.C A₀) ^ A₀)
  refine ⟨A, hA, ?_⟩
  intro G _ _ I _ _ n B _ _ _ J _ U basis R σ S c x hb o hR hσ C Vcap hC hV hσ1
    Cinv hCinv hchart hsmall P W hP hK hW hroot hWP hL hm₀ hRP hσP hcount hI hn hJ
    hAP hCP hVP M hperiod X _ _ hX hdim p hp hm base stride hs hsP
    τ ξ ε hτ hτP hξ hξ1 hξP hε hεP N hsize rank hrank hRank test htest T hT
    density D f hproject η hη hηP Z hZnorm V hVpos hmass law source projected
  let Q := allocatedFourierOutputBudget m P + P
  have hlog := allocatedFourierLogBudget_nonneg m hP
  have hF0 : 0 ≤ allocatedFourierOutputBudget m P := by
    unfold allocatedFourierOutputBudget
    positivity
  have hPQ : P ≤ Q := le_add_of_nonneg_left hF0
  have hFQ : allocatedFourierOutputBudget m P ≤ Q := le_add_of_nonneg_right hP
  have hQ : 0 ≤ Q := hP.trans hPQ
  have hcost : (Q + A₀) ^ A₀ ≤ (P + A) ^ A := by
    calc
      _ ≤ ((P + b) ^ b + P + A₀) ^ A₀ :=
        pow_le_pow_left₀ (by positivity) (by dsimp [Q]; linarith [hfourierBound P hP]) A₀
      _ ≤ _ := by simpa [Polynomial.eval₂_pow] using hbudget P hP
  obtain ⟨F, inst, frequency, coeff, _, hfrequency, hcoeff, happrox⟩ :=
    exists_allocated_coefficient_uniform_fourier B U basis hb o S C Vcap hC hV
      hR hσ hσ1 Cinv hCinv hchart hsmall hP hm₀ hK hRP hσP hcount hI hn hJ
      hAP hL hCP hVP hη hηP
  let _ := inst
  have houtputs := allocatedFourierOutputBudget_dominates m hP
  have he := Real.exp_le_exp.mpr hPQ
  exact hprojection B U basis S c x hQ (hK.trans hPQ) hW hroot (hWP.trans he) (hL.trans he)
    hperiod (hX.trans hPQ) (hdim.trans hPQ) frequency
    (fun a j e he' t => (hfrequency a j e he' t).trans
      (Real.exp_le_exp.mpr (houtputs.2.1.trans hFQ))) coeff
    (hcoeff.trans (Real.exp_le_exp.mpr (houtputs.2.2.trans hFQ))) p hp hm base stride hs
    (fun t => (hsP t).trans he) hτ (hτP.trans he) hξ hξ1 (hξP.trans he)
    hε (hεP.trans he) N (fun t => (Real.exp_le_exp.mpr hcost).trans (hsize t)) hrank
    ((Real.exp_le_exp.mpr hcost).trans hRank) test htest T hT density D f hproject
    hη.le happrox hZnorm hVpos hmass

end Erdos3.VectorPolynomial

end

end OAI
