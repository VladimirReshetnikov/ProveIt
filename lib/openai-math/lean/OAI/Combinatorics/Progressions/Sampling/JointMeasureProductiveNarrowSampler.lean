import OAI.Combinatorics.Progressions.Estimates.AllocatedCenteredJointProductivity
import OAI.Combinatorics.Progressions.Estimates.CanonicalEmptyLayerGeometry
import OAI.Combinatorics.Progressions.Geometry.ExplicitMixedUniformBox

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

theorem physicalSiteWidth_mono {K X : Type*} [Fintype K]
    (root : K → ℤ) {V W : Option K × X → ℝ} (h : ∀ z, V z ≤ W z) (x : X) :
    physicalSiteWidth root V x ≤ physicalSiteWidth root W x := by
  apply add_le_add (h (none,x))
  exact Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (h (some k,x)) (abs_nonneg _))

theorem narrowTrimmedSpatialWidths_fit {G J X : Type*} [Fintype G] [Fintype J]
    {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ1 : ξ ≤ 1)
    (root : G ⊕ J → ℤ) (hroot : (∑ k, |(root k : ℝ)|) ≤ W)
    (N : X → ℕ) (hN : ∀ x, 0 < N x) (x : X) :
    physicalSiteWidth root (narrowTrimmedSpatialWidths W τ ξ N) x ≤
      (spatialTrimMargin τ N x : ℝ) :=
  (physicalSiteWidth_mono root (narrowTrimmedSpatialWidths_le hW hτ hξ1 N hN) x).trans
    (spatialTrimMargin_fits hW hτ.le root hroot N x)

theorem narrow_jointIntegerPhysicalSite_mem_box {G J X : Type*}
    [Fintype G] [Fintype J] [Fintype X] [DecidableEq X]
    {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hτhalf : τ ≤ 1/2) (hξ1 : ξ ≤ 1)
    (root : G ⊕ J → ℤ) (hroot : (∑ k, |(root k : ℝ)|) ≤ W)
    (N : X → ℕ) (hN : ∀ x, 0 < N x) (hsize : ∀ x, 4 ≤ τ * (N x : ℝ))
    (z : trimmedIntegerBox N (spatialTrimMargin τ N) ×
      rectangularWeightIndices 0 (narrowTrimmedSpatialWidths (G := G) (J := J) W τ ξ N) 1) :
    jointIntegerPhysicalSite root (z.1.val,z.2.val) ∈ integerBox N :=
  jointIntegerPhysicalSite_mem_box root N (spatialTrimMargin τ N)
    (fun x => (spatialTrimMargin_proper hτhalf N hN hsize x).le) _
    (narrowTrimmedSpatialWidths_fit hW hτ hξ1 root hroot N hN) z

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_narrow_sampler_threshold (a b : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ P : ℝ, 0 ≤ P →
      (spatialSamplingBudget (2*P) + a)^a ≤ (P+A)^A ∧
      (spatialSamplingBudget (2*P) + b)^b ≤ (P+A)^A ∧
      10*P+128 ≤ (P+A)^A := by
  let base : Polynomial ℕ := 8*Polynomial.X+128
  let cost := (base+Polynomial.C a)^a+(base+Polynomial.C b)^b+10*Polynomial.X+128
  obtain ⟨A, hA, hbudget⟩ := exists_natPolynomial_eval_budget cost
  refine ⟨A, hA, fun P hP => ?_⟩
  have h := hbudget P hP
  have he : spatialSamplingBudget (2*P) = 8*P+128 := by unfold spatialSamplingBudget; ring
  have hc : (spatialSamplingBudget (2*P)+a)^a + (spatialSamplingBudget (2*P)+b)^b +
      10*P+128 ≤ (P+A)^A := by
    rw [he]
    simpa [cost, base, Polynomial.eval₂_pow] using h
  have hQ : 0 ≤ spatialSamplingBudget (2*P) := by unfold spatialSamplingBudget; positivity
  have ha : 0 ≤ (spatialSamplingBudget (2*P)+a)^a := by positivity
  have hb : 0 ≤ (spatialSamplingBudget (2*P)+b)^b := by positivity
  constructor
  · linarith
  constructor <;> linarith

theorem narrow_sampler_width_bounds {G J X : Type*} {P W τ ξ : ℝ}
    (hP : 0 ≤ P) (hW : 0 ≤ W) (hWP : W ≤ Real.exp P)
    (hτ : 0 < τ) (hτP : τ⁻¹ ≤ Real.exp P)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hξP : ξ⁻¹ ≤ Real.exp P)
    (N : X → ℕ) (hN : ∀ i, 0 < N i) :
    0 < spatialWidthFraction (2*P) (ξ*τ) ∧
    1/spatialWidthFraction (2*P) (ξ*τ) ≤ Real.exp (spatialSamplingBudget (2*P)) ∧
    ∀ z : Option (G ⊕ J) × X,
      spatialWidthFraction (2*P) (ξ*τ) * (N z.2 : ℝ) ≤ narrowTrimmedSpatialWidths W τ ξ N z := by
  have h2P : 0 ≤ 2*P := by positivity
  have hτξ : 0 < ξ*τ := mul_pos hξ hτ
  have hτξP : (ξ*τ)⁻¹ ≤ Real.exp (2*P) := by
    rw [mul_inv_rev]
    calc
      _ ≤ Real.exp P * Real.exp P := mul_le_mul hτP hξP (inv_nonneg.mpr hξ.le) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  refine ⟨spatialWidthFraction_pos (2*P) hτξ,
    spatialWidthFraction_inv_le h2P hτξ hτξP, ?_⟩
  intro z
  exact (spatialWidthFraction_le_allocated_width h2P hW
    (hWP.trans (Real.exp_le_exp.mpr (by linarith))) hτξ.le N z).trans
    (narrowTrimmedSpatialWidths_lower hW hτ hξ1 N hN z)

theorem narrow_sampler_residue_scale {G J X : Type*} {P W τ ξ : ℝ}
    (hP : 0 ≤ P) (hW : 0 ≤ W) (hWP : W ≤ Real.exp P)
    (hτ : 0 < τ) (hτP : τ⁻¹ ≤ Real.exp P)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hξP : ξ⁻¹ ≤ Real.exp P)
    (N q : X → ℕ) (hq : ∀ i, 0 < q i) (hqP : ∀ i, (q i : ℝ) ≤ Real.exp P)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hsize : ∀ i, Real.exp (10*P+128) ≤ (N i : ℝ)) :
    ∀ z : Option (G ⊕ J) × X, 8*(probabilityProfileLipschitz : ℝ) ≤
      residueProfileWidth q (narrowTrimmedSpatialWidths W τ ξ N) z := by
  have h2P : 0 ≤ 2*P := by positivity
  have hτξ : 0 < ξ*τ := mul_pos hξ hτ
  have hτξP : (ξ*τ)⁻¹ ≤ Real.exp (2*P) := by
    rw [mul_inv_rev]
    calc
      _ ≤ Real.exp P * Real.exp P := mul_le_mul hτP hξP (inv_nonneg.mpr hξ.le) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hB4 : W ≤ Real.exp (2*(2*P)) := hWP.trans (Real.exp_le_exp.mpr (by linarith))
  have hN (i) : 0 < N i := by exact_mod_cast (Real.exp_pos _).trans_le (hsize i)
  have hsz (i) : 64*(probabilityProfileLipschitz : ℝ)*(q i : ℝ)*(1+W) ≤ (ξ*τ)*(N i : ℝ) := by
    calc
      _ ≤ 64*(probabilityProfileLipschitz : ℝ)*(q i : ℝ)*(1+Real.exp (2*(2*P))) :=
        mul_le_mul_of_nonneg_left (by linarith only [hB4]) (by positivity)
      _ ≤ _ := spatial_scale_of_exp_size h2P hτξ hτξP (Nat.cast_nonneg _)
        ((hqP i).trans (Real.exp_le_exp.mpr (by linarith)))
        (hprofile.trans (Real.exp_le_exp.mpr (by linarith)))
        (by convert hsize i using 1; congr 2; ring)
  intro z
  exact (trimmedSpatialWidths_scale hW q hq N hsz z).trans
    (div_le_div_of_nonneg_right (narrowTrimmedSpatialWidths_lower hW hτ hξ1 N hN z)
      (Nat.cast_nonneg _))

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open Module Submodule MeasureTheory VectorPolynomial
open scoped BigOperators NNReal

theorem exists_joint_sampler_uniform_box_law (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {X G : Type*} [Fintype X] [DecidableEq X] [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
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
    (R σ : Fin m → ℝ) (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (_hσ1 : ∀ j, σ j ≤ 1)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cinv j * ‖x‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ)+1) * R j ≤ 1/4)
    (L₀ : ℕ) {P δ : ℝ} (_hP : 0 ≤ P) (_hδ : 0 < δ) (_hδsmall : δ ≤ 1/6)
    (_hδP : δ⁻¹ ≤ Real.exp P) (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) (_hL₀P : (L₀ : ℝ) ≤ Real.exp P)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (root : LayerSamplerVariables G I n B → ℤ) (_hroot : ∀ k, |(root k : ℝ)| ≤ Real.exp P)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val+1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : X → ℕ) (_hs : ∀ k, 0 < stride k)
    {Rrank S ρ : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (_hρ : 0 < ρ) (_hρP : 1/ρ ≤ Real.exp P)
    (H : X → ℝ) (_hsize : ∀ k, Real.exp ((P+A)^A) ≤ H k)
    (_hrank : ∀ j, HasLayerSamplingRank (j.val+1) H Rrank (U j) (p j))
    (_hRrank : Real.exp ((P+A)^A) ≤ Rrank)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty)
    (W : Option (LayerSamplerVariables G I n B) × X → ℝ) (hW : ∀ z, 0 < W z)
    (_hwidth : ∀ z, ρ * H z.2 ≤ W z)
    (N margin : X → ℕ) (_hmargin : ∀ i, 2 * margin i < N i)
    (_hfit : ∀ i, physicalSiteWidth root W i ≤ (margin i : ℝ)),
    let pa := fun (a : X → ℤ) j => translate (fun i => (a i : ℝ)) (p j)
    let hma := fun (a : X → ℤ) j => coefficients_translate_mem (U j) (fun i => (a i : ℝ)) (p j) (hm j)
    let D := fun a center => translatedSelectedPhysicalDensity (G := G) B U b hb o R σ hR hσ L₀
      (coefficientConstantCenter U center) (pa a) (hma a)
    let Q := trimmedIntegerBox N margin
    let Z := fun center => selectedJointDensityMass Q stride T W (fun a => D a center)
    ∃ hQ : Q.Nonempty,
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T W z,
    ∃ hD : ∀ center, 0 < Z center,
      (∀ center, |Z center-1| ≤ 3*δ ∧ 1/2 ≤ Z center ∧ Z center ≤ 3/2) ∧
      ∀ φ : (X → ℝ) → ℂ, (∀ v, ‖φ v‖ ≤ 1) →
        let f := fun center =>
          (selectedJointFiniteLaw Q hQ stride T W hW hZ (fun a => D a center)
            (fun a => translatedSelectedPhysicalDensity_nonneg (G := G) B U b hb o R σ hR hσ L₀
              (coefficientConstantCenter U center) (pa a) (hma a)) (hD center)).complexMean
            (fun z => φ ((fun i => (z.1.val i : ℝ)) + physicalAffineSite root z.2.val))
        Integrable f μ ∧
        ‖(∫ center, f center ∂μ) - (𝔼 x ∈ integerBox N, φ (fun i => (x i : ℝ)))‖ ≤
          12*δ + 2 * ∑ i, 2 * (margin i : ℝ) / N i := by
  obtain ⟨A, hA, hlaw⟩ := exists_mixed_selected_sampler_uniform_box_law m
  refine ⟨A, hA, ?_⟩
  intro X G _ _ _ I _ n B _ J _ U b hb o _ _ _ _ μ _ _ ν _ _
    R σ hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall L₀ P δ hP hδ hδsmall hδP
    hX hK hI hn hJ hAP hL₀P hCP hVP hRP hσP root hroot p hp hm stride hs Rrank S ρ
    hS hSP hstride hρ hρP H hsize hrank hRrank T hT W hW hwidth N margin hmargin hfit
    pa hma D Q Z
  obtain ⟨hZ, hlocal, hclose, hmix⟩ := hlaw B U b hb o μ ν R σ hR hσ hσ1 C V hC hV
    Cinv hCinv hchart hsmall L₀ hP hδ hδsmall hδP hX hK hI hn hJ hAP hL₀P hCP hVP
    hRP hσP root hroot p hp hm stride hs hS hSP hstride hρ hρP H hsize hrank hRrank
    T hT W hW hwidth N margin hmargin hfit
  have hQ : Q.Nonempty := trimmedIntegerBox_nonempty N margin hmargin
  have hjbounds (center) : Z center ∈ Set.Icc (1/2 : ℝ) (3/2) :=
    selectedJointDensityMass_bounds Q hQ stride T W _
      (fun a => ⟨(hclose a center).2.1, (hclose a center).2.2⟩)
  have hglobal (center) : 0 < Z center :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/2) (hjbounds center).1
  have hD0 (center) (a) := translatedSelectedPhysicalDensity_nonneg (G := G) B U b hb o R σ hR hσ L₀
    (coefficientConstantCenter U center) (pa a) (hma a)
  have hmeas (a) (z) : Measurable (fun center => D a center z) :=
    (translatedSelectedPhysicalDensity_measurable_center B U b hb o R σ hR hσ L₀ (pa a) (hma a) z).comp
      (coefficientConstantCenter_continuous U).measurable
  refine ⟨hQ, hZ, hglobal, ?_, ?_⟩
  · intro center
    exact ⟨selectedJointDensityMass_close Q hQ stride T W _ (fun a => (hclose a center).1),
      (hjbounds center).1, (hjbounds center).2⟩
  · intro φ hφ
    dsimp only
    constructor
    · have hi := (selectedJointReference Q hQ stride T W hW hZ).normalizedDensityTest_integrable μ
        (fun center z => D z.1.val center z.2.val)
        (fun z => hmeas z.1.val z.2.val) (fun center z => hD0 center z.1.val z.2.val)
        (fun center => by
          rw [selectedJointReference_densityMass Q hQ stride T W hW hZ (fun a => D a center)]
          exact hglobal center)
        (fun z => φ ((fun i => (z.1.val i : ℝ)) + physicalAffineSite root z.2.val))
        (fun z => hφ _)
      apply hi.congr
      filter_upwards [] with center
      exact (selectedJointFiniteLaw_complexMean Q hQ stride T W hW hZ
        (fun a => D a center) (hD0 center) (hglobal center)
        (fun a z => φ ((fun i => (a i : ℝ)) + physicalAffineSite root z))).symm
    · have h := selectedJointFiniteLaw_integral_local_comparison Q hQ stride T W hW hZ μ
        (fun center a => D a center) hmeas hD0 hglobal (fun center a => hlocal a center)
        (fun a z => φ ((fun i => (a i : ℝ)) + physicalAffineSite root z)) (fun a z => hφ _)
        (fun center a => (hclose a center).1)
      exact ((norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
        (add_le_add h (hmix φ hφ))).trans_eq (by ring)

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open Module Submodule MeasureTheory VectorPolynomial
open scoped BigOperators NNReal Classical

theorem exists_narrow_joint_sampler (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {X G S₀ : Type*} [Fintype X] [DecidableEq X] [Nonempty X] [Fintype G]
    [Fintype S₀] [DecidableEq S₀]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
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
    (R σ : Fin m → ℝ) (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (_hσ1 : ∀ j, σ j ≤ 1)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cinv j * ‖x‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ)+1) * R j ≤ 1/4)
    (L₀ : ℕ) {P δ : ℝ} (_hP : 0 ≤ P) (_hδ : 0 < δ) (_hδsmall : δ ≤ 1/6)
    (_hδP : δ⁻¹ ≤ Real.exp P) (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) (_hL₀P : (L₀ : ℝ) ≤ Real.exp P)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (site : S₀ → LayerSamplerVariables G I n B → ℤ) (_hsite : Function.Injective site)
    (rootBudget : ℝ) (_hrootBudget : 0 ≤ rootBudget) (_hrootBudgetP : rootBudget ≤ Real.exp P)
    (_hsitebound : ∀ q, (∑ k, |(site q k : ℝ)|) ≤ rootBudget)
    (ξ : ℝ) (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hξP : ξ⁻¹ ≤ Real.exp P)
    (τ : ℝ) (_hτ : 0 < τ) (_hτhalf : τ ≤ 1/2) (_hτP : τ⁻¹ ≤ Real.exp P)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val+1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : X → ℕ) (_hs : ∀ k, 0 < stride k)
    {Rrank S : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (N : X → ℕ) (_hsize : ∀ k, Real.exp ((P+A)^A) ≤ (N k : ℝ))
    (_hrank : ∀ j, HasLayerSamplingRank (j.val+1) (fun i => (N i : ℝ)) Rrank (U j) (p j))
    (_hRrank : Real.exp ((P+A)^A) ≤ Rrank)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty),
    let W := narrowTrimmedSpatialWidths (G := G)
      (J := PrincipalTupleIndex B (layerSamplerDegree I n)) rootBudget τ ξ N
    let Q := trimmedIntegerBox N (spatialTrimMargin τ N)
    let D := jointSelectedPhysicalDensity B U b hb o R σ hR hσ L₀ p hm
    let Z := fun center => selectedJointDensityMass Q stride T W (D center)
    ∃ hQ : Q.Nonempty,
    ∃ hW : ∀ z, 0 < W z,
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T W z,
    ∃ hD : ∀ center, 0 < Z center,
    let law := fun center => selectedJointFiniteLaw Q hQ stride T W hW hZ (D center)
      (jointSelectedPhysicalDensity_nonneg B U b hb o R σ hR hσ L₀ p hm center) (hD center)
    (∀ center, |Z center-1| ≤ 3*δ ∧ 1/2 ≤ Z center ∧ Z center ≤ 3/2) ∧
    (∀ root : LayerSamplerVariables G I n B → ℤ,
      (∑ k, |(root k : ℝ)|) ≤ rootBudget → ∀ z : Q × rectangularWeightIndices 0 W 1,
        jointIntegerPhysicalSite root (z.1.val,z.2.val) ∈ integerBox N) ∧
    (∀ center, ∃ c : ∀ j, U j, coefficientConstantCenter U center =
      -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (constantCoefficientArray U (fun s => c s.1))) ∧
      ∀ z, 0 < (law center).weight z →
        allocatedAffineDensity B U b hb o hR hσ
          (selectedLayerSamplerScale B U b R σ hR hσ L₀) p hm c
          (fun k v => (jointIntegerFrame (z.1.val,z.2.val) k v : ℝ)) ≠ 0) ∧
    (∀ root : LayerSamplerVariables G I n B → ℤ,
      (∑ k, |(root k : ℝ)|) ≤ rootBudget → ∀ φ : (X → ℝ) → ℂ, (∀ v, ‖φ v‖ ≤ 1) →
      let f := fun center => (law center).complexMean
        (fun z => φ (fun i => (jointIntegerPhysicalSite root (z.1.val,z.2.val) i : ℝ)))
      Integrable f μ ∧
      ‖(∫ center, f center ∂μ) - (𝔼 x ∈ integerBox N, φ (fun i => (x i : ℝ)))‖ ≤
        12*δ + 2 * (Fintype.card X : ℝ) * τ) ∧
    ∀ center, (law center).mean
      (fun z => noninjectivityIndicator (fun q => jointIntegerPhysicalSite (site q) (z.1.val,z.2.val))) ≤ δ := by
  obtain ⟨A₀, _, hsampler⟩ := exists_joint_sampler_uniform_box_law m
  obtain ⟨A₁, _, hcollisionBudget⟩ := exists_selectedCollisionLog_bound m
  obtain ⟨A, hA, hbudget⟩ := exists_narrow_sampler_threshold A₀ A₁
  refine ⟨A, hA, ?_⟩
  intro X G S₀ _ _ _ _ _ _ I _ n B _ J _ U basis hb o _ _ _ _ μ _ _ ν _ _
    R σ hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall L₀ P δ hP hδ hδsmall hδP
    hX hK hI hn hJ hAP hL₀P hCP hVP hRP hσP site hsite
    rootBudget hrootBudget hrootBudgetP hsitebound ξ hξ hξ1 hξP τ hτ hτhalf hτP p hp hm
    stride hs Rrank S hS hSP hstride N hsize hrank hRrank T hT
    W Q D Z
  let P' := spatialSamplingBudget (2*P)
  have h2P : 0 ≤ 2*P := mul_nonneg (by norm_num) hP
  have hPP' : P ≤ P' := by dsimp [P', spatialSamplingBudget]; linarith
  have hP' : 0 ≤ P' := hP.trans hPP'
  have hexp := Real.exp_le_exp.mpr hPP'
  obtain ⟨hcut₀, hcut₁, hcutLarge⟩ := hbudget P hP
  have hlarge (i) : Real.exp (10*P+128) ≤ (N i : ℝ) :=
    (Real.exp_le_exp.mpr hcutLarge).trans (hsize i)
  have hN (i) : 0 < N i := by exact_mod_cast (Real.exp_pos _).trans_le (hlarge i)
  have hW : ∀ z, 0 < W z := narrowTrimmedSpatialWidths_pos hrootBudget hτ hξ N hN
  obtain ⟨hρ, hρP, hwidth⟩ := narrow_sampler_width_bounds (G := G)
    (J := PrincipalTupleIndex B (layerSamplerDegree I n))
    hP hrootBudget hrootBudgetP hτ hτP hξ hξ1 hξP N hN
  have hmarginSize (i) : 4 ≤ τ*(N i : ℝ) :=
    spatialTrimMargin_size_of_exp_size hP hτ hτP
      ((Real.exp_le_exp.mpr (by linarith : 5*P+128 ≤ 10*P+128)).trans (hlarge i))
  have hmargin := spatialTrimMargin_proper hτhalf N hN hmarginSize
  have hroot (root : LayerSamplerVariables G I n B → ℤ)
      (hr : (∑ k, |(root k : ℝ)|) ≤ rootBudget) (k) : |(root k : ℝ)| ≤ Real.exp P' :=
    ((Finset.single_le_sum (fun j _ => abs_nonneg (root j : ℝ)) (Finset.mem_univ k)).trans hr).trans
      (hrootBudgetP.trans hexp)
  have hsample (root : LayerSamplerVariables G I n B → ℤ)
      (hr : (∑ k, |(root k : ℝ)|) ≤ rootBudget) :=
    hsampler B U basis hb o μ ν R σ hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall L₀
      hP' hδ hδsmall (hδP.trans hexp) (hX.trans hPP') (hK.trans hPP')
      (fun j => (hI j).trans hPP') (fun j => (hn j).trans hPP') (fun j => (hJ j).trans hPP')
      (hAP.trans hexp) (hL₀P.trans hexp) (fun j => (hCP j).trans hexp) (fun j => (hVP j).trans hexp)
      (fun j => (hRP j).trans hexp) (fun j => (hσP j).trans hexp) root (hroot root hr) p hp hm
      stride hs hS (hSP.trans hexp) hstride hρ hρP (fun i => (N i : ℝ))
      (fun i => (Real.exp_le_exp.mpr hcut₀).trans (hsize i)) hrank
      ((Real.exp_le_exp.mpr hcut₀).trans hRrank) T hT W hW hwidth N
      (spatialTrimMargin τ N) hmargin
      (narrowTrimmedSpatialWidths_fit hrootBudget hτ hξ1 root hr N hN)
  obtain ⟨hQ, hZ, hD, hclose, _⟩ := hsample 0 (by simpa using hrootBudget)
  have hscale := narrow_sampler_residue_scale (G := G)
    (J := PrincipalTupleIndex B (layerSamplerDegree I n)) hP hrootBudget hrootBudgetP
    hτ hτP hξ hξ1 hξP N stride hs (fun i => (hstride i).trans hSP) hAP hlarge
  refine ⟨hQ, hW, hZ, hD, hclose, ?_, ?_, ?_, ?_⟩
  · intro root hr z
    exact narrow_jointIntegerPhysicalSite_mem_box hrootBudget hτ hτhalf hξ1 root hr N hN hmarginSize z
  · intro center
    obtain ⟨c, hc⟩ := exists_subtractive_constant_center U center
    refine ⟨c, hc, ?_⟩
    intro z hz
    have hd := (selectedJointFiniteLaw_support Q hQ stride T W hW hZ (D center)
      (jointSelectedPhysicalDensity_nonneg B U basis hb o R σ hR hσ L₀ p hm center) (hD center) z hz).2
    change 0 < jointSelectedPhysicalDensity B U basis hb o R σ hR hσ L₀ p hm center z.1.val z.2.val at hd
    rw [jointSelectedPhysicalDensity_eq_allocated B U basis hb o R σ hR hσ L₀ p hm center c hc] at hd
    exact hd.ne'
  · intro root hr φ hφ
    obtain ⟨_, _, _, _, hmix⟩ := hsample root hr
    obtain ⟨hi, he⟩ := hmix φ hφ
    have hDfun (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U) :=
      jointSelectedPhysicalDensity_function B U basis hb o R σ hR hσ L₀ p hm center
    constructor
    · simpa only [D, hDfun, Q, jointIntegerPhysicalSite_cast] using hi
    · have he' := he.trans (add_le_add le_rfl (spatialTrimMargin_error_bound N hN hmarginSize))
      simpa only [D, hDfun, Q, jointIntegerPhysicalSite_cast] using he'

  · intro center
    let i : X := Classical.choice inferInstance
    exact selectedJointFiniteLaw_collision_small Q hQ m site hsite i hP' hδ (hδP.trans hexp)
      (hK.trans hPP') (fun q => hroot (site q) (hsitebound q))
      stride hs (((hstride i).trans hSP).trans hexp) T hT W hW hZ hscale hρ
      (hρP.trans (Real.exp_le_exp.mpr (le_spatialSamplingBudget hP')))
      ((Real.exp_le_exp.mpr (hcollisionBudget P' hP')).trans
        ((Real.exp_le_exp.mpr hcut₁).trans (hsize i)))
      (fun k => hwidth (some k,i)) (D center)
      (jointSelectedPhysicalDensity_nonneg B U basis hb o R σ hR hσ L₀ p hm center)
      (hD center) (hclose center).2.1
      (fun a z => translatedSelectedPhysicalDensity_le_exp B U basis hb o C V hC hV R σ hR hσ hσ1
        Cinv hCinv hchart hsmall L₀ hP' (hK.trans hPP')
        (fun j => (hRP j).trans hexp) (fun j => (hσP j).trans hexp)
        (fun j => (hI j).trans hPP') (fun j => (hn j).trans hPP') (fun j => (hJ j).trans hPP')
        (hAP.trans hexp) (hL₀P.trans hexp) (fun j => (hCP j).trans hexp) (fun j => (hVP j).trans hexp)
        (coefficientConstantCenter U center) (fun j => translate (fun t => (a t : ℝ)) (p j))
        (fun j => coefficients_translate_mem (U j) (fun t => (a t : ℝ)) (p j) (hm j)) z)

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open Module Submodule MeasureTheory VectorPolynomial
open scoped BigOperators NNReal Classical

theorem exists_joint_productive_narrow_sampler (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {X G S₀ : Type*} [Fintype X] [DecidableEq X] [Nonempty X] [Fintype G]
    [Fintype S₀] [DecidableEq S₀] [Nonempty S₀]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
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
    (R σ : Fin m → ℝ) (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (_hσ1 : ∀ j, σ j ≤ 1)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cinv j * ‖x‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ)+1) * R j ≤ 1/4)
    (L₀ : ℕ) {P δ : ℝ} (_hP : 0 ≤ P) (_hδ : 0 < δ) (_hδsmall : δ ≤ 1/6)
    (_hδP : δ⁻¹ ≤ Real.exp P) (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) (_hL₀P : (L₀ : ℝ) ≤ Real.exp P)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (site : S₀ → LayerSamplerVariables G I n B → ℤ) (_hsite : Function.Injective site)
    (rootBudget : ℝ) (_hrootBudget : 0 ≤ rootBudget) (_hrootBudgetP : rootBudget ≤ Real.exp P)
    (_hsitebound : ∀ q, (∑ k, |(site q k : ℝ)|) ≤ rootBudget)
    (ξ : ℝ) (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hξP : ξ⁻¹ ≤ Real.exp P)
    (τ : ℝ) (_hτ : 0 < τ) (_hτhalf : τ ≤ 1/2) (_hτP : τ⁻¹ ≤ Real.exp P)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val+1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : X → ℕ) (_hs : ∀ k, 0 < stride k)
    {Rrank S : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (N : X → ℕ) (_hsize : ∀ k, Real.exp ((P+A)^A) ≤ (N k : ℝ))
    (_hrank : ∀ j, HasLayerSamplingRank (j.val+1) (fun i => (N i : ℝ)) Rrank (U j) (p j))
    (_hRrank : Real.exp ((P+A)^A) ≤ Rrank)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty),
    let W := narrowTrimmedSpatialWidths (G := G)
      (J := PrincipalTupleIndex B (layerSamplerDegree I n)) rootBudget τ ξ N
    let Q := trimmedIntegerBox N (spatialTrimMargin τ N)
    let D := jointSelectedPhysicalDensity B U b hb o R σ hR hσ L₀ p hm
    let Z := fun center => selectedJointDensityMass Q stride T W (D center)
    ∃ hQ : Q.Nonempty,
    ∃ hW : ∀ z, 0 < W z,
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T W z,
    ∃ hD : ∀ center, 0 < Z center,
    let law := fun center => selectedJointFiniteLaw Q hQ stride T W hW hZ (D center)
      (jointSelectedPhysicalDensity_nonneg B U b hb o R σ hR hσ L₀ p hm center) (hD center)
    ∀ (test : (X → ℝ) → ℝ), (∀ x, |test x| ≤ 1) →
    ∀ gain : ℝ, 0 < gain →
    δ ≤ gain / 16 → 12*δ + 2*(Fintype.card X : ℝ)*τ ≤ gain / 8 →
    gain ≤ (𝔼 x ∈ integerBox N, test (fun i => (x i : ℝ))) →
    (gain / 4 ≤ ∫ center, (law center).mass (Finset.univ.filter (fun z =>
      Function.Injective (fun q => jointIntegerPhysicalSite (site q) (z.1.val,z.2.val)) ∧
      gain / 2 ≤ 𝔼 q : S₀, test (fun i => (jointIntegerPhysicalSite (site q)
        (z.1.val,z.2.val) i : ℝ)))) ∂μ) ∧
    (∀ center : CoefficientTorus (K := LayerSamplerVariables G I n B) U,
      ∃ c : ∀ j, U j,
      coefficientConstantCenter U center =
        -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
          (constantCoefficientArray U (fun s => c s.1))) ∧
      ∀ z, 0 < (law center).weight z →
        allocatedAffineDensity B U b hb o hR hσ
          (selectedLayerSamplerScale B U b R σ hR hσ L₀) p hm c
          (fun k v => (jointIntegerFrame (z.1.val,z.2.val) k v : ℝ)) ≠ 0) ∧
      ∀ z : Q × rectangularWeightIndices 0 W 1, ∀ q,
        jointIntegerPhysicalSite (site q) (z.1.val,z.2.val) ∈ integerBox N := by
  obtain ⟨A, hA, hsampler⟩ := exists_narrow_joint_sampler m
  refine ⟨A, hA, ?_⟩
  intro X G S₀ _ _ _ _ _ _ _ I _ n B _ J _ U b hb o _ _ _ _ μ _ _ ν _ _
    R σ hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall L₀ P δ hP hδ hδsmall hδP
    hX hK hI hn hJ hAP hL₀P hCP hVP hRP hσP site hsite
    rootBudget hrootBudget hrootBudgetP hsitebound ξ hξ hξ1 hξP τ hτ hτhalf hτP p hp hm
    stride hs Rrank S hS hSP hstride N hsize hrank hRrank T hT W Q D Z
  obtain ⟨hQ, hW, hZ, hD, _, hinside, hdensity, hmarginal, hcollision⟩ :=
    hsampler B U b hb o μ ν R σ hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall L₀
      hP hδ hδsmall hδP hX hK hI hn hJ hAP hL₀P hCP hVP hRP hσP site hsite
      rootBudget hrootBudget hrootBudgetP hsitebound ξ hξ hξ1 hξP τ hτ hτhalf hτP p hp hm
      stride hs hS hSP hstride N hsize hrank hRrank T hT
  refine ⟨hQ, hW, hZ, hD, ?_⟩
  intro law test htest gain hgain hbad herror hscore
  let image := fun (z : Q × rectangularWeightIndices 0 W 1) (q : S₀) =>
    jointIntegerPhysicalSite (site q) (z.1.val,z.2.val)
  have hcm (q : S₀) := hmarginal (site q) (hsitebound q)
    (fun x => (test x : ℂ)) (fun x => by simpa only [Complex.norm_real, Real.norm_eq_abs] using htest x)
  have hmeanCast : (𝔼 x ∈ integerBox N, (test (fun i => (x i : ℝ)) : ℂ)) =
      ((𝔼 x ∈ integerBox N, test (fun i => (x i : ℝ)) : ℝ) : ℂ) := by
    simp only [Finset.expect_eq_sum_div_card, Complex.ofReal_div, Complex.ofReal_sum, Complex.ofReal_natCast]
  have hDm (a : X → ℤ) (z) : Measurable (fun center => D center a z) :=
    jointSelectedPhysicalDensity_measurable_center B U b hb o R σ hR hσ L₀ p hm a z
  have hproductive := selectedJointFiniteLaw_integral_productivity Q hQ stride T W hW hZ
    μ D hDm (jointSelectedPhysicalDensity_nonneg B U b hb o R σ hR hσ L₀ p hm) hD
    (FiniteProbabilityWeights.uniform S₀)
    (fun a z q => jointIntegerPhysicalSite (site q) (a,z))
    (fun x => test (fun i => (x i : ℝ)))
    hgain herror hscore (fun x => (le_abs_self _).trans (htest _))
    (fun q => ⟨(hcm q).1, by rw [← hmeanCast]; exact (hcm q).2⟩)
    (fun center => (hcollision center).trans hbad)
  refine ⟨?_, hdensity, fun z q => hinside (site q) (hsitebound q) z⟩
  simpa only [FiniteProbabilityWeights.uniform_mean, image] using hproductive

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open Module Submodule MeasureTheory VectorPolynomial
open scoped BigOperators NNReal Classical

theorem exists_productive_narrow_sampler (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {X G S₀ : Type*} [Fintype X] [DecidableEq X] [Nonempty X] [Fintype G]
    [Fintype S₀] [DecidableEq S₀] [Nonempty S₀]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
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
    (R σ : Fin m → ℝ) (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (_hσ1 : ∀ j, σ j ≤ 1)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cinv j * ‖x‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ)+1) * R j ≤ 1/4)
    (L₀ : ℕ) {P δ : ℝ} (_hP : 0 ≤ P) (_hδ : 0 < δ) (_hδsmall : δ ≤ 1/6)
    (_hδP : δ⁻¹ ≤ Real.exp P) (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) (_hL₀P : (L₀ : ℝ) ≤ Real.exp P)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (site : S₀ → LayerSamplerVariables G I n B → ℤ) (_hsite : Function.Injective site)
    (rootBudget : ℝ) (_hrootBudget : 0 ≤ rootBudget) (_hrootBudgetP : rootBudget ≤ Real.exp P)
    (_hsitebound : ∀ q, (∑ k, |(site q k : ℝ)|) ≤ rootBudget)
    (ξ : ℝ) (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hξP : ξ⁻¹ ≤ Real.exp P)
    (τ : ℝ) (_hτ : 0 < τ) (_hτhalf : τ ≤ 1/2) (_hτP : τ⁻¹ ≤ Real.exp P)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val+1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : X → ℕ) (_hs : ∀ k, 0 < stride k)
    {Rrank S : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (N : X → ℕ) (_hsize : ∀ k, Real.exp ((P+A)^A) ≤ (N k : ℝ))
    (_hrank : ∀ j, HasLayerSamplingRank (j.val+1) (fun i => (N i : ℝ)) Rrank (U j) (p j))
    (_hRrank : Real.exp ((P+A)^A) ≤ Rrank)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty),
    let W := narrowTrimmedSpatialWidths (G := G)
      (J := PrincipalTupleIndex B (layerSamplerDegree I n)) rootBudget τ ξ N
    let Q := trimmedIntegerBox N (spatialTrimMargin τ N)
    let D := jointSelectedPhysicalDensity B U b hb o R σ hR hσ L₀ p hm
    let Z := fun center => selectedJointDensityMass Q stride T W (D center)
    ∃ hQ : Q.Nonempty,
    ∃ hW : ∀ z, 0 < W z,
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T W z,
    ∃ hD : ∀ center, 0 < Z center,
    let law := fun center => selectedJointFiniteLaw Q hQ stride T W hW hZ (D center)
      (jointSelectedPhysicalDensity_nonneg B U b hb o R σ hR hσ L₀ p hm center) (hD center)
    ∀ (test : (X → ℝ) → ℝ), (∀ x, |test x| ≤ 1) →
    ∀ gain : ℝ, 0 < gain →
    δ ≤ gain / 16 → 12*δ + 2*(Fintype.card X : ℝ)*τ ≤ gain / 8 →
    gain ≤ (𝔼 x ∈ integerBox N, test (fun i => (x i : ℝ))) →
    ∃ (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U) (c : ∀ j, U j),
      coefficientConstantCenter U center =
        -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
          (constantCoefficientArray U (fun s => c s.1))) ∧
      gain / 4 ≤ (law center).mass (Finset.univ.filter (fun z =>
        Function.Injective (fun q => jointIntegerPhysicalSite (site q) (z.1.val,z.2.val)) ∧
        gain / 2 ≤ 𝔼 q : S₀, test (fun i => (jointIntegerPhysicalSite (site q) (z.1.val,z.2.val) i : ℝ)))) ∧
      (∀ z, 0 < (law center).weight z →
        allocatedAffineDensity B U b hb o hR hσ
          (selectedLayerSamplerScale B U b R σ hR hσ L₀) p hm c
          (fun k v => (jointIntegerFrame (z.1.val,z.2.val) k v : ℝ)) ≠ 0) ∧
      ∀ z : Q × rectangularWeightIndices 0 W 1, ∀ q,
        jointIntegerPhysicalSite (site q) (z.1.val,z.2.val) ∈ integerBox N := by
  obtain ⟨A, hA, hsampler⟩ := exists_narrow_joint_sampler m
  refine ⟨A, hA, ?_⟩
  intro X G S₀ _ _ _ _ _ _ _ I _ n B _ J _ U b hb o _ _ _ _ μ _ _ ν _ _
    R σ hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall L₀ P δ hP hδ hδsmall hδP
    hX hK hI hn hJ hAP hL₀P hCP hVP hRP hσP site hsite
    rootBudget hrootBudget hrootBudgetP hsitebound ξ hξ hξ1 hξP τ hτ hτhalf hτP p hp hm
    stride hs Rrank S hS hSP hstride N hsize hrank hRrank T hT W Q D Z
  obtain ⟨hQ, hW, hZ, hD, _, hinside, hdensity, hmarginal, hcollision⟩ :=
    hsampler B U b hb o μ ν R σ hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall L₀
      hP hδ hδsmall hδP hX hK hI hn hJ hAP hL₀P hCP hVP hRP hσP site hsite
      rootBudget hrootBudget hrootBudgetP hsitebound ξ hξ hξ1 hξP τ hτ hτhalf hτP p hp hm
      stride hs hS hSP hstride N hsize hrank hRrank T hT
  refine ⟨hQ, hW, hZ, hD, ?_⟩
  intro law test htest gain hgain hbad herror hscore
  let image := fun (z : Q × rectangularWeightIndices 0 W 1) (q : S₀) =>
    jointIntegerPhysicalSite (site q) (z.1.val,z.2.val)
  have hcm (q : S₀) := hmarginal (site q) (hsitebound q)
    (fun x => (test x : ℂ)) (fun x => by simpa only [Complex.norm_real, Real.norm_eq_abs] using htest x)
  have hmeanCast : (𝔼 x ∈ integerBox N, (test (fun i => (x i : ℝ)) : ℂ)) =
      ((𝔼 x ∈ integerBox N, test (fun i => (x i : ℝ)) : ℝ) : ℂ) := by
    simp only [Finset.expect_eq_sum_div_card, Complex.ofReal_div, Complex.ofReal_sum, Complex.ofReal_natCast]
  obtain ⟨center, hproductive⟩ := exists_productive_injective_center_of_complex_marginals μ law
    (FiniteProbabilityWeights.uniform S₀) image (fun x => test (fun i => (x i : ℝ)))
    hgain herror hscore (fun x => (le_abs_self _).trans (htest _))
    (fun q => (hcm q).1)
    (fun q => by rw [← hmeanCast]; exact (hcm q).2)
    (fun center => (hcollision center).trans hbad)
  obtain ⟨c, hc, hd⟩ := hdensity center
  refine ⟨center, c, hc, ?_, hd, fun z q => hinside (site q) (hsitebound q) z⟩
  simpa only [FiniteProbabilityWeights.uniform_mean, image] using hproductive

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open Module Submodule MeasureTheory VectorPolynomial
open scoped BigOperators NNReal Classical

theorem exists_joint_measure_productive_narrow_sampler (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {X G S₀ : Type*} [Fintype X] [DecidableEq X] [Nonempty X] [Fintype G]
    [Fintype S₀] [DecidableEq S₀] [Nonempty S₀]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
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
    (R σ : Fin m → ℝ) (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (_hσ1 : ∀ j, σ j ≤ 1)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cinv j * ‖x‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ)+1) * R j ≤ 1/4)
    (L₀ : ℕ) {P δ : ℝ} (_hP : 0 ≤ P) (_hδ : 0 < δ) (_hδsmall : δ ≤ 1/6)
    (_hδP : δ⁻¹ ≤ Real.exp P) (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) (_hL₀P : (L₀ : ℝ) ≤ Real.exp P)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (site : S₀ → LayerSamplerVariables G I n B → ℤ) (_hsite : Function.Injective site)
    (rootBudget : ℝ) (_hrootBudget : 0 ≤ rootBudget) (_hrootBudgetP : rootBudget ≤ Real.exp P)
    (_hsitebound : ∀ q, (∑ k, |(site q k : ℝ)|) ≤ rootBudget)
    (ξ : ℝ) (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hξP : ξ⁻¹ ≤ Real.exp P)
    (τ : ℝ) (_hτ : 0 < τ) (_hτhalf : τ ≤ 1/2) (_hτP : τ⁻¹ ≤ Real.exp P)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val+1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : X → ℕ) (_hs : ∀ k, 0 < stride k)
    {Rrank S : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (N : X → ℕ) (_hsize : ∀ k, Real.exp ((P+A)^A) ≤ (N k : ℝ))
    (_hrank : ∀ j, HasLayerSamplingRank (j.val+1) (fun i => (N i : ℝ)) Rrank (U j) (p j))
    (_hRrank : Real.exp ((P+A)^A) ≤ Rrank)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty),
    let W := narrowTrimmedSpatialWidths (G := G)
      (J := PrincipalTupleIndex B (layerSamplerDegree I n)) rootBudget τ ξ N
    let Q := trimmedIntegerBox N (spatialTrimMargin τ N)
    let D := jointSelectedPhysicalDensity B U b hb o R σ hR hσ L₀ p hm
    let Z := fun center => selectedJointDensityMass Q stride T W (D center)
    ∃ hQ : Q.Nonempty,
    ∃ hW : ∀ z, 0 < W z,
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T W z,
    ∃ hD : ∀ center, 0 < Z center,
    let law := fun center => selectedJointFiniteLaw Q hQ stride T W hW hZ (D center)
      (jointSelectedPhysicalDensity_nonneg B U b hb o R σ hR hσ L₀ p hm center) (hD center)
    ∀ (test : (X → ℝ) → ℝ), (∀ x, |test x| ≤ 1) →
    ∀ gain : ℝ, 0 < gain →
    δ ≤ gain / 16 → 12*δ + 2*(Fintype.card X : ℝ)*τ ≤ gain / 8 →
    gain ≤ (𝔼 x ∈ integerBox N, test (fun i => (x i : ℝ))) →
    let productive := Finset.univ.filter (fun z : Q × rectangularWeightIndices 0 W 1 =>
      Function.Injective (fun q => jointIntegerPhysicalSite (site q) (z.1.val,z.2.val)) ∧
      gain / 2 ≤ 𝔼 q : S₀, test (fun i => (jointIntegerPhysicalSite (site q)
        (z.1.val,z.2.val) i : ℝ)))
    let joint := centeredFiniteProbabilityMeasure μ law
    IsProbabilityMeasure joint ∧
      MeasurableSet {z : CoefficientTorus (K := LayerSamplerVariables G I n B) U ×
        (Q × rectangularWeightIndices 0 W 1) | z.2 ∈ productive} ∧
      gain / 4 ≤ joint.real {z | z.2 ∈ productive} ∧
      (∀ᵐ z ∂joint, ∃ c : ∀ j, U j,
        coefficientConstantCenter U z.1 =
          -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
            (constantCoefficientArray U (fun s => c s.1))) ∧
        allocatedAffineDensity B U b hb o hR hσ
          (selectedLayerSamplerScale B U b R σ hR hσ L₀) p hm c
          (fun k v => (jointIntegerFrame (z.2.1.val,z.2.2.val) k v : ℝ)) ≠ 0) ∧
      ∀ z : Q × rectangularWeightIndices 0 W 1, ∀ q,
        jointIntegerPhysicalSite (site q) (z.1.val,z.2.val) ∈ integerBox N := by
  obtain ⟨A, hA, hsampler⟩ := exists_joint_productive_narrow_sampler m
  refine ⟨A, hA, ?_⟩
  intro X G S₀ _ _ _ _ _ _ _ I _ n B _ J _ U b hb o _ _ _ _ μ _ _ ν _ _
    R σ hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall L₀ P δ hP hδ hδsmall hδP
    hX hK hI hn hJ hAP hL₀P hCP hVP hRP hσP site hsite
    rootBudget hrootBudget hrootBudgetP hsitebound ξ hξ hξ1 hξP τ hτ hτhalf hτP p hp hm
    stride hs Rrank S hS hSP hstride N hsize hrank hRrank T hT W Q D Z
  obtain ⟨hQ, hW, hZ, hD, hproductive⟩ :=
    hsampler B U b hb o μ ν R σ hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall L₀
      hP hδ hδsmall hδP hX hK hI hn hJ hAP hL₀P hCP hVP hRP hσP site hsite
      rootBudget hrootBudget hrootBudgetP hsitebound ξ hξ hξ1 hξP τ hτ hτhalf hτP p hp hm
      stride hs hS hSP hstride N hsize hrank hRrank T hT
  refine ⟨hQ, hW, hZ, hD, ?_⟩
  intro law test htest gain hgain hbad herror hscore productive joint
  obtain ⟨hmass, hdensity, hinside⟩ :=
    hproductive test htest gain hgain hbad herror hscore
  have hDm (a : X → ℤ) (z) : Measurable (fun center => D center a z) :=
    jointSelectedPhysicalDensity_measurable_center B U b hb o R σ hR hσ L₀ p hm a z
  have hweight (z : Q × rectangularWeightIndices 0 W 1) :
      Measurable (fun center => (law center).weight z) :=
    selectedJointFiniteLaw_weight_measurable Q hQ stride T W hW hZ D hDm
      (jointSelectedPhysicalDensity_nonneg B U b hb o R σ hR hσ L₀ p hm) hD z
  let Qgood := fun z : CoefficientTorus (K := LayerSamplerVariables G I n B) U ×
      (Q × rectangularWeightIndices 0 W 1) => ∃ c : ∀ j, U j,
    coefficientConstantCenter U z.1 =
      -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (constantCoefficientArray U (fun s => c s.1))) ∧
    allocatedAffineDensity B U b hb o hR hσ
      (selectedLayerSamplerScale B U b R σ hR hσ L₀) p hm c
      (fun k v => (jointIntegerFrame (z.2.1.val,z.2.2.val) k v : ℝ)) ≠ 0
  have hgood (center) (z : Q × rectangularWeightIndices 0 W 1)
      (hz : 0 < (law center).weight z) : Qgood (center, z) := by
    obtain ⟨c, hc, hsupport⟩ := hdensity center
    exact ⟨c, hc, hsupport z hz⟩
  obtain ⟨hprob, hmeas, hmassJoint, hgoodJoint⟩ :=
    centeredFiniteProbabilityMeasure_productive_family μ law hweight productive Qgood hgood hmass
  exact ⟨hprob, hmeas, hmassJoint, hgoodJoint, hinside⟩

end Erdos3.BooleanCubeKernel

end

end OAI
