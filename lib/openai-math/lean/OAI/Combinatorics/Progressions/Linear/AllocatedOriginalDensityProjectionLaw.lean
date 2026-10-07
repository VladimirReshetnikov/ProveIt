import OAI.Combinatorics.Progressions.Linear.AllocatedOriginalSourceProjection

namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

universe uX

theorem exists_allocated_original_density_projection_law (m q : ℕ) :
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
    ∀ law : FiniteProbabilityWeights (PrincipalIntegerTuples B (layerSamplerDegree I n)
      (Fin q) (allocatedPrincipalSides B U basis S)),
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
  obtain ⟨A₀, _, hprojection⟩ := exists_allocated_mixture_density_projection_law m q
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
    hwidths hmass law
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

end OAI
