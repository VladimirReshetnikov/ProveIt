import OAI.Combinatorics.Progressions.Dynamics.AllocatedFixedScaleCollisionBudget
import OAI.Combinatorics.Progressions.Sampling.JointMeasureProductiveNarrowSampler

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
variable (hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
variable (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cinv j * ‖x‖)
variable (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1/4)

local notation "K" => LayerSamplerVariables G I n B

include hC hV hσ1 hCinv hchart hsmall in

theorem allocatedFixedScaleJoint_collision_small
    {X Tsite : Type*} [Fintype X] [DecidableEq X] [Fintype Tsite] [DecidableEq Tsite]
    (point : (X → ℤ) → (Option K × X → ℤ) → CoefficientTorus («K» := K) U)
    {P δ : ℝ} (hP : 0 ≤ P) (hm : (m : ℝ) ≤ P)
    (hK : (Fintype.card K : ℝ) ≤ P)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent K (j.val+1)) : ℝ) ≤ P)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (hn : ∀ j, (n j : ℝ) ≤ P)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hSP : (S.value : ℝ) ≤ Real.exp P)
    (hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (bases : Finset (X → ℤ)) (hbases : bases.Nonempty)
    (site : Tsite → K → ℤ) (hsite : Function.Injective site) (i : X)
    (hδ : 0 < δ) (hδP : δ⁻¹ ≤ Real.exp P)
    (hbound : ∀ s k, |(site s k : ℝ)| ≤ Real.exp P)
    (modulus : X → ℕ) (hmodulus : ∀ i, 0 < modulus i)
    (hmodP : (modulus i : ℝ) ≤ Real.exp P)
    (cells : Finset (ColumnResiduePattern (Option K) X modulus)) (hcells : cells.Nonempty)
    (W : Option K × X → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus cells W z)
    (hscale : ∀ z, 8*(probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth modulus W z)
    {ρ N : ℝ} (hρ : 0 < ρ) (hρP : 1/ρ ≤ Real.exp (spatialSamplingBudget P))
    (hN : Real.exp (allocatedFixedScaleCollisionLog m P) ≤ N)
    (hwidth : ∀ k, ρ*N ≤ W (some k,i)) :
    let D := fun a z => allocatedCoefficientDensity B U b hb o hR hσ S (point a z)
    ∀ (hD0 : ∀ a z, 0 ≤ D a z)
      (hD : 0 < selectedJointDensityMass bases modulus cells W D),
    1/2 ≤ selectedJointDensityMass bases modulus cells W D →
    (selectedJointFiniteLaw bases hbases modulus cells W hW hZ D hD0 hD).mean
      (fun z => noninjectivityIndicator
        (fun t => jointIntegerPhysicalSite (site t) (z.1.val,z.2.val))) ≤ δ := by
  intro D hD0 hD hlower
  apply selectedJointFiniteLaw_collision_small_with_cap bases hbases site hsite i hP hδ hδP
    hK hbound modulus hmodulus hmodP cells hcells W hW hZ hscale hρ hρP
    hN hwidth D hD0 hD hlower
  intro a z
  exact allocatedCoefficientDensity_fixedScale_le_exp B U b hb o hR hσ S C V hC hV
    hσ1 Cinv hCinv hchart hsmall hP hm hK hRP hσP hcount hI hn hJ hAP hSP hCP hVP _

include hC hV hσ1 hCinv hchart hsmall in

theorem allocatedCenteredJointDensity_collision_small
    {X Tsite : Type*} [Fintype X] [DecidableEq X] [Fintype Tsite] [DecidableEq Tsite]
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hmem : ∀ j e, coefficients (poly j) e ∈ U j)
    (center : CoefficientTorus («K» := K) U)
    {P δ : ℝ} (hP : 0 ≤ P) (hm : (m : ℝ) ≤ P)
    (hK : (Fintype.card K : ℝ) ≤ P)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent K (j.val+1)) : ℝ) ≤ P)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (hn : ∀ j, (n j : ℝ) ≤ P)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hSP : (S.value : ℝ) ≤ Real.exp P)
    (hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (bases : Finset (X → ℤ)) (hbases : bases.Nonempty)
    (site : Tsite → K → ℤ) (hsite : Function.Injective site) (i : X)
    (hδ : 0 < δ) (hδP : δ⁻¹ ≤ Real.exp P)
    (hbound : ∀ s k, |(site s k : ℝ)| ≤ Real.exp P)
    (modulus : X → ℕ) (hmodulus : ∀ i, 0 < modulus i)
    (hmodP : (modulus i : ℝ) ≤ Real.exp P)
    (cells : Finset (ColumnResiduePattern (Option K) X modulus)) (hcells : cells.Nonempty)
    (W : Option K × X → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus cells W z)
    (hscale : ∀ z, 8*(probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth modulus W z)
    {ρ N : ℝ} (hρ : 0 < ρ) (hρP : 1/ρ ≤ Real.exp (spatialSamplingBudget P))
    (hN : Real.exp (allocatedFixedScaleCollisionLog m P) ≤ N)
    (hwidth : ∀ k, ρ*N ≤ W (some k,i)) :
    let D := allocatedCenteredJointDensity B U b hb o hR hσ S poly hmem center
    ∀ (hD0 : ∀ a z, 0 ≤ D a z)
      (hD : 0 < selectedJointDensityMass bases modulus cells W D),
    1/2 ≤ selectedJointDensityMass bases modulus cells W D →
    (selectedJointFiniteLaw bases hbases modulus cells W hW hZ D hD0 hD).mean
      (fun z => noninjectivityIndicator
        (fun t => jointIntegerPhysicalSite (site t) (z.1.val,z.2.val))) ≤ δ := by
  exact allocatedFixedScaleJoint_collision_small B U b hb o hR hσ S C V hC hV
    hσ1 Cinv hCinv hchart hsmall
    (fun a z => coefficientConstantCenter U center +
      affineSampleCoefficientTorus U poly hmem
        (fun k i => (jointIntegerFrame (a, z) k i : ℝ)))
    hP hm hK hRP hσP hcount hI hn hJ hAP hSP hCP hVP bases hbases site hsite i
    hδ hδP hbound modulus hmodulus hmodP cells hcells W hW hZ hscale hρ hρP hN hwidth

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

theorem exists_allocated_narrow_joint_collision (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {X G Sites : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype G] [Fintype Sites] [DecidableEq Sites]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale (G := G) B U b R σ)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (_hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cinv j * ‖x‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1/4)
    {P δ : ℝ} (_hP : 0 ≤ P) (_hm : (m : ℝ) ≤ P)
    (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (_hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) ≤ P)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (_hSP : (S.value : ℝ) ≤ Real.exp P)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hmem : ∀ j e, coefficients (poly j) e ∈ U j)
    (site : Sites → LayerSamplerVariables G I n B → ℤ) (_hsite : Function.Injective site)
    (_hδ : 0 < δ) (_hδP : δ⁻¹ ≤ Real.exp P)
    {W τ ξ : ℝ} (_hW : 0 ≤ W) (_hWP : W ≤ Real.exp P)
    (_hroot : ∀ q, (∑ k, |(site q k : ℝ)|) ≤ W)
    (_hτ : 0 < τ) (_hτP : τ⁻¹ ≤ Real.exp P)
    (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hξP : ξ⁻¹ ≤ Real.exp P)
    (N stride : X → ℕ) (_hs : ∀ i, 0 < stride i) (_hsP : ∀ i, (stride i : ℝ) ≤ Real.exp P)
    (_hsize : ∀ i, Real.exp ((P + A)^A) ≤ (N i : ℝ))
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
    (_hcells : cells.Nonempty) (bases : Finset (X → ℤ)) (hbases : bases.Nonempty),
    let widths := narrowTrimmedSpatialWidths (G := G)
      (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    ∀ (hwidths : ∀ z, 0 < widths z)
      (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells widths z)
      (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U),
    let density := allocatedCenteredJointDensity B U b hb o hR hσ S poly hmem center
    ∀ (hD : 0 < selectedJointDensityMass bases stride cells widths density),
    1/2 ≤ selectedJointDensityMass bases stride cells widths density →
    (selectedJointFiniteLaw bases hbases stride cells widths hwidths hmass density
      (allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S poly hmem center) hD).mean
      (fun z => noninjectivityIndicator
        (fun q => jointIntegerPhysicalSite (site q) (z.1.val,z.2.val))) ≤ δ := by
  obtain ⟨A₁, _, hcollisionBudget⟩ := exists_allocatedFixedScaleCollisionLog_bound m
  obtain ⟨A, hA, hbudget⟩ := exists_narrow_sampler_threshold 0 A₁
  refine ⟨A, hA, ?_⟩
  intro X G Sites _ _ _ _ _ _ I _ n B _ J _ U b hb o R σ hR hσ S _
    C V hC hV hσ1 Cinv hCinv hchart hsmall P δ hP hm hK hRP hσP hcount hI hn hJ
    hAP hSP hCP hVP poly hmem site hsite hδ hδP W τ ξ hW hWP hroot
    hτ hτP hξ hξ1 hξP N stride hs hsP hsize cells hcells bases hbases
    widths hwidths hmass center density hD hlower
  let P' := spatialSamplingBudget (2*P)
  have hPP' : P ≤ P' := by dsimp [P', spatialSamplingBudget]; linarith
  have hP' : 0 ≤ P' := hP.trans hPP'
  have hexp := Real.exp_le_exp.mpr hPP'
  obtain ⟨_, hcut, hlargeLog⟩ := hbudget P hP
  have hlarge i : Real.exp (10*P+128) ≤ (N i : ℝ) :=
    (Real.exp_le_exp.mpr hlargeLog).trans (hsize i)
  have hN i : 0 < N i := by exact_mod_cast (Real.exp_pos _).trans_le (hlarge i)
  obtain ⟨hρ, hρP, hwidth⟩ := narrow_sampler_width_bounds (G := G)
    (J := PrincipalTupleIndex B (layerSamplerDegree I n))
    hP hW hWP hτ hτP hξ hξ1 hξP N hN
  have hscale := narrow_sampler_residue_scale (G := G)
    (J := PrincipalTupleIndex B (layerSamplerDegree I n))
    hP hW hWP hτ hτP hξ hξ1 hξP N stride hs hsP hAP hlarge
  let i : X := Classical.choice inferInstance
  apply allocatedFixedScaleJoint_collision_small B U b hb o hR hσ S C V hC hV hσ1
    Cinv hCinv hchart hsmall
    (fun a z => coefficientConstantCenter U center + affineSampleCoefficientTorus U poly hmem
      (fun k v => (jointIntegerFrame (a,z) k v : ℝ)))
    hP' (hm.trans hPP') (hK.trans hPP')
    (fun j => (hRP j).trans hexp) (fun j => (hσP j).trans hexp)
    (fun j => (hcount j).trans hPP') (fun j => (hI j).trans hPP')
    (fun j => (hn j).trans hPP') (fun j => (hJ j).trans hPP')
    (hAP.trans hexp) (hSP.trans hexp) (fun j => (hCP j).trans hexp) (fun j => (hVP j).trans hexp)
    bases hbases site hsite i hδ (hδP.trans hexp)
    (fun q k => ((Finset.single_le_sum (fun j _ => abs_nonneg (site q j : ℝ))
      (Finset.mem_univ k)).trans (hroot q)).trans (hWP.trans hexp))
    stride hs ((hsP i).trans hexp) cells hcells widths hwidths hmass hscale hρ
    (hρP.trans (Real.exp_le_exp.mpr (le_spatialSamplingBudget hP')))
    ((Real.exp_le_exp.mpr (hcollisionBudget P' hP')).trans
      ((Real.exp_le_exp.mpr hcut).trans (hsize i)))
    (fun k => hwidth (some k,i))
    (allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S poly hmem center) hD hlower

end Erdos3.VectorPolynomial

end

end OAI
