import OAI.Combinatorics.Progressions.Estimates.AllocatedNarrowJointCollision

namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

def AllocatedFixedScaleProductiveStatement (m A : ℕ) : Prop :=
    ∀ {X G : Type*} [Fintype X] [DecidableEq X] [Nonempty X] [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
    (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (_hσ1 : ∀ j, σ j ≤ 1)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ V j)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    {P : ℝ} (_hP : 0 ≤ P) (_hmSize : (m : ℝ) ≤ P)
    (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ P)
    (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (_hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) (_hLP : (S.value : ℝ) ≤ Real.exp P)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : X → ℕ) (_hs : ∀ d, 0 < stride d) (_hsP : ∀ d, (stride d : ℝ) ≤ Real.exp P)
    {W τ ξ : ℝ} (_hW : 0 ≤ W) (_hWP : W ≤ Real.exp P)
    (_hτ : 0 < τ) (_hτP : τ⁻¹ ≤ Real.exp P) (_hτhalf : τ ≤ 1 / 2)
    (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hξP : ξ⁻¹ ≤ Real.exp P)
    (N : X → ℕ) (_hsize : ∀ d, Real.exp ((P + A) ^ A) ≤ (N d : ℝ))
    {rank : ℝ} (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (p j))
    (_hRank : Real.exp ((P + A) ^ A) ≤ rank)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty),
    let widths := narrowTrimmedSpatialWidths (G := G)
      (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let bases := trimmedIntegerBox N (spatialTrimMargin τ N)
    let density := allocatedCenteredJointDensity B U basis hb o hR hσ S p hm
    ∃ (_hN : ∀ i, 0 < N i) (hwidths : ∀ z, 0 < widths z)
      (hmargin : ∀ i, 2 * spatialTrimMargin τ N i < N i)
      (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride T widths z)
      (hD : ∀ center, 0 < selectedJointDensityMass bases stride T widths (density center)),
    let law := fun center => selectedJointFiniteLaw bases
      (trimmedIntegerBox_nonempty N _ hmargin) stride T widths hwidths hmass
      (density center) (allocatedCenteredJointDensity_nonneg B U basis hb o hR hσ S p hm center)
      (hD center)
    (∀ center,
      let Z := selectedJointDensityMass bases stride T widths (density center)
      |Z - 1| ≤ Real.exp (-P) ∧ Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧ Z⁻¹ ≤ 2) ∧
    ∀ {Sites : Type*} [Fintype Sites] [DecidableEq Sites] [Nonempty Sites]
      (site : Sites → LayerSamplerVariables G I n B → ℤ),
      Function.Injective site → (∀ q, (∑ k, |(site q k : ℝ)|) ≤ W) →
    ∀ (test : (X → ℝ) → ℝ), (∀ x, |test x| ≤ 1) →
    ∀ gain : ℝ, 0 < gain → Real.exp (-P) ≤ gain / 16 →
      12 * positiveProjectionAccuracy P + 2 * (Fintype.card X : ℝ) * τ ≤ gain / 8 →
      gain ≤ (𝔼 x ∈ integerBox N, test (fun i => (x i : ℝ))) →
    let productive := Finset.univ.filter (fun z : bases × rectangularWeightIndices 0 widths 1 =>
      Function.Injective (fun q => jointIntegerPhysicalSite (site q) (z.1.val,z.2.val)) ∧
        gain / 2 ≤ 𝔼 q : Sites, test
          (fun i => (jointIntegerPhysicalSite (site q) (z.1.val,z.2.val) i : ℝ)))
    let joint := centeredFiniteProbabilityMeasure μ law
    IsProbabilityMeasure joint ∧
      MeasurableSet {z : CoefficientTorus (K := LayerSamplerVariables G I n B) U ×
        (bases × rectangularWeightIndices 0 widths 1) | z.2 ∈ productive} ∧
      gain / 4 ≤ joint.real {z | z.2 ∈ productive} ∧
      (∀ᵐ z ∂joint, ∃ c : ∀ j, U j,
        coefficientConstantCenter U z.1 =
          -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
            (constantCoefficientArray U (fun s => c s.1))) ∧
        allocatedAffineDensity B U basis hb o hR hσ S p hm c
          (fun k v => (jointIntegerFrame (z.2.1.val,z.2.2.val) k v : ℝ)) ≠ 0) ∧
      ∀ z : bases × rectangularWeightIndices 0 widths 1, ∀ q,
        jointIntegerPhysicalSite (site q) (z.1.val,z.2.val) ∈ integerBox N

theorem exists_allocated_fixedScale_productive_joint_measure (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ AllocatedFixedScaleProductiveStatement m A := by
  obtain ⟨A₁, _, hmarginal⟩ := exists_allocated_fixedScale_joint_marginal m
  obtain ⟨A₂, _, hcollision⟩ := exists_allocated_narrow_joint_collision m
  let A := max (max A₁ A₂) 256
  have hA : 256 ≤ A := le_max_right _ _
  have hA₁ : A₁ ≤ A := (le_max_left _ _).trans (le_max_left _ _)
  have hA₂ : A₂ ≤ A := (le_max_right _ _).trans (le_max_left _ _)
  refine ⟨A, by omega, ?_⟩
  intro X G _ _ _ _ I _ n B _ J _ U basis R σ S hb o _ _ _ _ μ _ _ ν _ _
    hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall P hP hmSize hK hX hdim
    hRP hσP hcount hI hn hJ hAP hLP hCP hVP p hp hm stride hs hsP W τ ξ
    hW hWP hτ hτP hτhalf hξ hξ1 hξP N hsize rank hrank hRank T hT widths bases density
  have hthreshold (a : ℕ) (ha : a ≤ A) :
      Real.exp ((P + a) ^ a) ≤ Real.exp ((P + A) ^ A) := by
    have hAr : (256 : ℝ) ≤ A := by exact_mod_cast hA
    have har : (a : ℝ) ≤ A := by exact_mod_cast ha
    apply Real.exp_le_exp.mpr
    exact (pow_le_pow_left₀ (by positivity)
      (by linarith only [har] : P + (a : ℝ) ≤ P + A) a).trans
      (pow_le_pow_right₀ (by linarith only [hP, hAr] : (1 : ℝ) ≤ P + A) ha)
  obtain ⟨hN, hwidths, hmargin, hmass, hD, hnormal, hmarginal⟩ :=
    hmarginal B U basis S hb o μ ν hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall
      hP hmSize hK hX hdim hRP hσP hcount hI hn hJ hAP hLP hCP hVP p hp hm
      stride hs hsP hW hWP hτ hτP hτhalf hξ hξ1 hξP N
      (fun i => (hthreshold A₁ hA₁).trans (hsize i)) hrank
      ((hthreshold A₁ hA₁).trans hRank) T hT
  refine ⟨hN, hwidths, hmargin, hmass, hD, ?_⟩
  intro law
  refine ⟨hnormal, ?_⟩
  intro Sites _ _ _ site hsite hrootSum test htest gain hgain hbad herror hscore productive joint
  have hroot q k : |(site q k : ℝ)| ≤ Real.exp P :=
    ((Finset.single_le_sum (fun j _ => abs_nonneg (site q j : ℝ))
      (Finset.mem_univ k)).trans (hrootSum q)).trans hWP
  have hmarg q := hmarginal (site q) (hroot q) (hrootSum q)
    (fun x => (test x : ℂ))
    (fun x => by simpa only [Complex.norm_real, Real.norm_eq_abs] using htest x)
  have hmeanCast : (𝔼 x ∈ integerBox N, (test (fun i => (x i : ℝ)) : ℂ)) =
      ((𝔼 x ∈ integerBox N, test (fun i => (x i : ℝ)) : ℝ) : ℂ) := by
    simp only [Finset.expect_eq_sum_div_card, Complex.ofReal_div,
      Complex.ofReal_sum, Complex.ofReal_natCast]
  have hprod := allocatedCenteredJoint_productivity B U basis hb o hR hσ S p hm μ
    bases (trimmedIntegerBox_nonempty N _ hmargin) stride T widths hwidths hmass hD
    site (fun x => test (fun i => (x i : ℝ))) hgain herror hscore
    (fun x => (le_abs_self _).trans (htest _))
    (fun q => by
      simpa only [jointIntegerPhysicalSite_cast, hmeanCast] using hmarg q)
    (fun center => (hcollision B U basis hb o hR hσ S C V hC hV hσ1 Cinv hCinv hchart hsmall
      hP hmSize hK hRP hσP hcount hI hn hJ hAP hLP hCP hVP p hm site hsite
      (Real.exp_pos (-P)) (by simpa only [← Real.exp_neg, neg_neg] using
        (le_rfl : Real.exp P ≤ Real.exp P))
      hW hWP hrootSum hτ hτP hξ hξ1 hξP N stride hs hsP
      (fun i => (hthreshold A₂ hA₂).trans (hsize i)) T hT bases
      (trimmedIntegerBox_nonempty N _ hmargin) hwidths hmass center (hD center)
      (hnormal center).2.1.1).trans hbad)
  refine ⟨hprod.1, hprod.2.1, hprod.2.2.1, hprod.2.2.2, ?_⟩
  have hmarginSize i : 4 ≤ τ * (N i : ℝ) :=
    spatialTrimMargin_size_of_exp_size hP hτ hτP
      ((spatial_threshold_large hP hA).trans (hsize i))
  intro z q
  exact narrow_jointIntegerPhysicalSite_mem_box hW hτ hτhalf hξ1 (site q)
    (hrootSum q) N hN hmarginSize z

end Erdos3.VectorPolynomial

end

end OAI
