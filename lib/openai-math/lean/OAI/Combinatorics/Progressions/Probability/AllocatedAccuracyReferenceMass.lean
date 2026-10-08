/- Modified for ProveIt: use direct product monotonicity for the dimension
bound in exists_allocated_accuracy_reference_mass_bound, avoiding a Lean 4.32
nlinarith timeout. All upstream theorem statements are unchanged. -/
import OAI.Combinatorics.Progressions.Estimates.AllocatedReferenceErrorWindowBound
import OAI.Combinatorics.Progressions.Fourier.AllocatedProjectedFourierData
import OAI.Combinatorics.Progressions.Sampling.AllocatedUnifiedSamplingBudget

namespace OAI

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators

theorem referenceProxyMass_exp_bound (dim : ℕ) (X : Type*) [Fintype X]
    {P D W L Z mass Etail : ℝ} (hP : 0 ≤ P) (hdim : ((dim + 1 : ℕ) : ℝ) ≤ P)
    (hX : (Fintype.card X : ℝ) ≤ P) (hL : 1 ≤ L) (hW : 0 ≤ W)
    (hD : D ≤ Real.exp P) (hWL : W ≤ D * L) (hZ : 0 < Z) (hZi : Z⁻¹ ≤ 2)
    (hmass : mass ≤ (coarseReferenceMassConstant dim X W L + Etail) / Z)
    (htail : Etail ≤ (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
      (((1 + W) / L) ^ dim) ^ Fintype.card X) :
    mass ≤ Real.exp (coefficientErrorVolumeLog P + 4) := by
  let V := (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
    (((1 + W) / L) ^ dim) ^ Fintype.card X
  have hprofile := smoothProbabilityProfile_pos_zero
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have hVE : V ≤ Real.exp (coefficientErrorVolumeLog P) :=
    referenceErrorVolumeFactor_exp_bound dim X hP hdim hX hL hW hD hWL
  have hten : (10 : ℝ) ≤ Real.exp 4 := by
    calc
      _ ≤ (2 : ℝ) ^ 4 := by norm_num
      _ ≤ (Real.exp 1) ^ 4 := pow_le_pow_left₀ (by norm_num)
        (by linarith [Real.add_one_le_exp (1 : ℝ)]) 4
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hbase : coarseReferenceMassConstant dim X W L = 4 * V := by
    dsimp only [coarseReferenceMassConstant, V]
    ring
  calc
    mass ≤ (4 * V + Etail) * Z⁻¹ := by simpa only [hbase, div_eq_mul_inv] using hmass
    _ ≤ (5 * V) * Z⁻¹ := mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.mpr hZ.le)
    _ ≤ (5 * V) * 2 := mul_le_mul_of_nonneg_left hZi (by positivity)
    _ = 10 * V := by ring
    _ ≤ Real.exp 4 * Real.exp (coefficientErrorVolumeLog P) :=
      mul_le_mul hten hVE hV (Real.exp_pos 4).le
    _ = _ := by rw [← Real.exp_add, add_comm]

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

theorem exists_allocated_retained_reference_mass (m q : ℕ) :
    ∃ T : ℕ, 2 ≤ T ∧ ∀ {G : Type*} [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
    (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox (Fin q) S.value)
    (C V : Fin m → ℝ≥0) (d : ℕ) (_hd : 0 < d)
    (g : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin q) (allocatedPrincipalSides B U b S) →
      EuclideanJetLayers U (fun j => BoundedBooleanJet (Fin q) (j.val + 1)) → ℝ)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (_hg0 : ∀ y z, 0 ≤ g y z)
    (_hgi : ∀ y, Integrable (g y) (Measure.pi (fun j =>
      Measure.pi (fun _ : BoundedBooleanJet (Fin q) (j.val+1) => ν j))))
    (_hgm : ∀ y, (∫ z, g y z ∂(Measure.pi (fun j =>
      Measure.pi (fun _ : BoundedBooleanJet (Fin q) (j.val+1) => ν j)))) = 1)
    (A : ℕ) {P : ℝ} (_hP : 0 ≤ P)
    (_hdata : allocatedProjectedFourierData B U b S C V d g A P)
    (_hm : (m : ℝ) ≤ P)
    (_hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (_hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) ≤ P)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    {X : Type*} [Fintype X] [DecidableEq X]
    {Pmass : ℝ} (_hQ : allocatedJetFourierBudget m q A P ≤ Pmass)
    (_hX : (Fintype.card X : ℝ) ≤ Pmass)
    (_hdim : (Fintype.card (Option (Fin q) × X) : ℝ) ≤ Pmass)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val+1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j)
    (N stride : X → ℕ) (_hs : ∀ t, 0 < stride t)
    {Rrank W τ ξ ρ : ℝ} (_hW : 0 ≤ W) (_hτ : 0 < τ) (_hξ : ξ ≤ 1) (_hρ : 0 < ρ)
    (_hτP : 1 / τ ≤ Real.exp Pmass) (_hstride : ∀ t, (stride t : ℝ) ≤ Real.exp Pmass)
    (_hsize : ∀ t, Real.exp ((Pmass + T)^T) ≤ (N t : ℝ))
    (_hrank : ∀ j, HasLayerSamplingRank (j.val+1) (fun t => (N t : ℝ)) Rrank (U j) (p j))
    (_hRank : Real.exp ((Pmass + T)^T) ≤ Rrank)
    (_hspatial : ∀ t, 8*(1+W)*(stride t : ℝ)*ρ ≤ (ξ*τ)*(N t : ℝ))
    (_hρ8 : 8*(probabilityProfileLipschitz : ℝ) ≤ ρ)
    (_hρshift : 2 * (Fintype.card (Option (LayerSamplerVariables G I n B)) *
      (2 * allocatedPhysicalEntryBudget B U b S c)) ≤ ρ)
    (y y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin q) (allocatedPrincipalSides B U b S))
    (base : X → ℤ) (residue : ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride),
    let H := trimmedSpatialRootScale τ N stride
    (∑ v ∈ spatialWindow H 4, g y (physicalCubeEuclideanSample U d p hm
      (physicalResidueReconstruction (allocatedPhysicalCubeRoot B U b S c x y₀)
        (allocatedPhysicalCubeDirections B U b S x y₀) base
        (boundedColumnResidueRepresentative stride residue) stride v))) ≤
      (4 * (30 / smoothProbabilityProfile 0)^Fintype.card (Option (Fin q) × X)) *
        (∏ t, ∏ _i : Unit ⊕ Fin q, H t) := by
  obtain ⟨T, hT, hmass⟩ := exists_coarse_reference_jet_mass m q
  refine ⟨T, hT, ?_⟩
  intro G _ I _ n B _ J _ U b R σ S c x C V d hd g _ ν _ _ hg0 hgi hgm A P hP hdata
    hm₀ hvars hRP hσP hcount hI hn hJ hAP hCP hVP X _ _ Pmass hQ hX hdim
    p hp hm N stride hs Rrank W τ ξ ρ hW hτ hξ hρ hτP hstride hsize hrank hRank
    hspatial hρ8 hρshift y y₀ base residue H
  obtain ⟨Index, inst, frequency, coeff, hfreq, hcoeff, herr⟩ :=
    hdata.2 hm₀ hvars hRP hσP hcount hI hn hJ hAP hCP hVP y
      (show (0 : ℝ) < 1 by norm_num) (by simpa using Real.one_le_exp hP)
  let _ := inst
  have hPmass := (allocatedJetFourierBudget_nonneg m q A hP).trans hQ
  have hN (t : X) : 0 < N t := by
    exact_mod_cast (Real.exp_pos _).trans_le (hsize t)
  have hgeometry := allocatedNarrow_reference_jet_geometry B U b S c x y₀ N stride hN hs
    hW hτ hξ hρ hspatial hρ8 hρshift
  have hcoverP : (d : ℝ) ≤ Real.exp Pmass := hdata.1.trans (Real.exp_le_exp.mpr hQ)
  exact hmass hPmass hX hdim U ν frequency
    (fun a j e he t => (hfreq a j e he t).trans (Real.exp_le_exp.mpr hQ)) coeff
    (hcoeff.trans (Real.exp_le_exp.mpr hQ)) p hp hm d hd hcoverP stride hs hτ hτP
    hstride (fun t => (N t : ℝ)) hsize hrank hRank
    (allocatedPhysicalCubeRoot B U b S c x y₀) (allocatedPhysicalCubeDirections B U b S x y₀)
    base residue H (fun t => (hgeometry t).1) (fun t => (hgeometry t).2.1)
    (fun t => (hgeometry t).2.2.1) (fun t => (hgeometry t).2.2.2)
    (g y) (hg0 y) (hgi y) (hgm y) herr

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable (m dim : ℕ)

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) ((j : ℕ) + 1))
local notation "jetRows" => (fun j : Fin m => (Subtype.val : BoundedBooleanJet (Fin dim) ((j : ℕ) + 1) → Finset (Fin dim)))

theorem exists_allocated_fixed_reference_mass_bound :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ {G : Type*} [Fintype G] [DecidableEq G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale (G := G) B U b R σ) (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (d : ℕ) [NeZero d] (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (modulus : ℕ) [NeZero modulus]
    (_hperiod : ∀ j, integerScalarLattice (jets j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (jetRows j)).mulVecLin.range)
    {X : Type*} [Fintype X] [DecidableEq X]
    (q : X → ℕ) (_hq : ∀ t, 0 < q t)
    (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
      (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
      PrincipalAxisTuples (α := Fin dim) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
    (N : X → ℕ) (_hN : ∀ t, 0 < N t)
    {W τ ξ ρ : ℝ} (_hW : 0 ≤ W) (_hτ : 0 < τ) (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hρ : 0 < ρ)
    (_hsizeSp : ∀ t, 8 * (1 + W) * (q t : ℝ) * ρ ≤ (ξ * τ) * (N t : ℝ))
    (_hρ8 : 8 * (probabilityProfileLipschitz : ℝ) ≤ ρ)
    (_hρshift : 2 * (Fintype.card (Option (LayerSamplerVariables G I n B)) *
      (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0))) ≤ ρ)
    (base : X → ℤ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
    (_hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells
      (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j)
    {P Rrank ε : ℝ} (_hP : 0 ≤ P) (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ P)
    (_hτP : 1 / τ ≤ Real.exp P) (_hstride : ∀ t, (q t : ℝ) ≤ Real.exp P)
    (_hε : 0 < ε) (_hεP : 1 / ε ≤ Real.exp P)
    (_hsize : ∀ t, Real.exp ((P + K) ^ K) ≤ (N t : ℝ))
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) Rrank (U j) (p j))
    (_hRank : Real.exp ((P + K) ^ K) ≤ Rrank)
    (η : ℝ≥0) {δf L : ℝ} (_hδf : 0 < δf) (_hL : 0 ≤ L)
    (_hamb : (Fintype.card (JetAmbientIndex jets J) : ℝ) ≤ L) (_hδL : δf⁻¹ ≤ Real.exp L),
    let A := Real.toNNReal (coefficientDeckPeriodCap jets Q modulus)
    (allocatedErrorKernelLip B U b S (O := jets) η A C V : ℝ) ≤ Real.exp L →
    Real.exp ((2 * L + 2) ^ 4) ≤ Real.exp P →
    Real.exp (2 * L * (2 * L + 2) ^ 4) * allocatedErrorKernelCap B U b S (O := jets) η A V ≤ Real.exp P →
    ∀ (hRefined : 0 < residueRefinedPeriod modulus q),
    let _ : NeZero (residueRefinedPeriod modulus q) := ⟨hRefined.ne'⟩
    ∀ (s : ∀ j, jets j ↪ BoundedIntegerExponent G (j.val+1))
    (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (jetRows j)).submatrix id (s j)).det ≠ 0)
    (residue : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
      (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
      ∀ j, Matrix (jets j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    (hlengths : ∀ t, (Fintype.card (Fin dim)+1)*residueRefinedPeriod modulus q ≤
      principalAxisLength (fun a => ¬allocatedGridAxis (I := I) U b S.value a) (allocatedPrincipalSides B U b S) t)
    (_href : ∀ u r, principalResidueLabel (residueRefinedPeriod modulus q) (reference u r) = r)
    (_hr : ∀ u r v,
      (allocatedLongResidueWeights B U b S (residueRefinedPeriod modulus q) hRefined r hlengths).weight v ≠ 0 → ∀ j,
      integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u jetRows j v) modulus = residue u r j)
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cinv j * ‖v‖)
    (_hsmall : ∀ j, R j ≤ allocatedPhysicalChartRadius (G := G) B (Fin dim) Cinv 1 j)
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (g : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S) →
      EuclideanJetLayers U jets → ℝ)
    (_hg : ∀ y, Continuous (g y)) (_hg0 : ∀ y z, 0 ≤ g y z)
    (_hlaw : ∀ y, (realDensityMeasure μ (fun z => allocatedCoefficientDensity B U b hb o hR hσ S
        (quotientIntegerCover (coefficientIntegerLattice (K := LayerSamplerVariables G I n B) U) d z))).map
      (euclideanCoefficientJetMap U (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
        (allocatedPhysicalCubeDirections B U b S x y) jetRows) =
      realDensityMeasure (Measure.pi (fun j => Measure.pi (fun _ : jets j => ν j))) (g y))
    (_hprojected : ∀ y y₀ (a : ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q),
      (∑ v ∈ spatialWindow (trimmedSpatialRootScale τ N q) 4,
        g y (physicalCubeEuclideanSample U d p hm (physicalResidueReconstruction
          (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y₀)
          (allocatedPhysicalCubeDirections B U b S x y₀) base
          (boundedColumnResidueRepresentative q a) q v))) ≤
        (4 * (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X)) *
          (∏ t, ∏ _i : Unit ⊕ Fin dim, trimmedSpatialRootScale τ N q t))
    {M : ℕ} (_hM : 0 < M) (selection : Fin dim ↪ G)
    (_hx : GoodScalarKernelTuple selection (1/(M : ℝ)) M x) (_hdim : Fintype.card (Fin dim) ≤ m+1)
    (_hσ1 : ∀ j, σ j ≤ 1)
    {Pc Ec Tc : ℝ} (_hPc : 0 ≤ Pc) (_hEc : 0 ≤ Ec) (_hTc : 0 ≤ Tc)
    (_hη : 0 < (η : ℝ)) (_hη1 : (η : ℝ) ≤ 1)
    (_hMP : (M : ℝ) ≤ Real.exp Pc) (_hRP : ∀ j, R j ≤ Real.exp Pc)
    (_hRi : ∀ j, (R j)⁻¹ ≤ Real.exp Pc) (_hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp Pc)
    (_hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ)+1 ≤ Real.exp Pc)
    (_hηE : (η : ℝ)⁻¹ ≤ Real.exp Ec)
    (_hlarge : Real.exp (allocatedRefinedJointLengthLog (G := G) B (Fin dim) jets Pc Ec Tc) ≤ S.value)
    (_hi : ∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val+1) (jetRows j) (s j) (hA j) (1/(M : ℝ)))
    (_hbound : (residueRefinedPeriod modulus q : ℝ) ≤ Real.exp Tc)
    {Z : ℝ} (_hZ : 0 < Z),
    let Vsp := (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
      (((1 + W) / S.value) ^ dim) ^ Fintype.card X
    let Merr := (η : ℝ) * A *
      (2 * (∑ j, (C j : ℝ) * ((Fintype.card (J j) : ℝ) + 1)) + 1) ^
        Fintype.card (Σ a : LayerSamplerAxis I n, jets a.1)
    allocatedRefinedReferenceSpatialMass (τ := τ) (ξ := ξ) (W := W)
      B U b hR hσ S x jetRows X modulus s hA q reference residue hb o bW d N base cells
      (physicalCubeEuclideanSample U d p hm) Z ≤
      (coarseReferenceMassConstant dim X W S.value + Vsp * (Merr + 2 * δf + ε)) / Z ∧
    ∀ {Pbound D : ℝ}, 0 ≤ Pbound → ((dim + 1 : ℕ) : ℝ) ≤ Pbound →
      (Fintype.card X : ℝ) ≤ Pbound → D ≤ Real.exp Pbound → W ≤ D * S.value →
      Z⁻¹ ≤ 2 → Merr + 2 * δf + ε ≤ 1 →
      allocatedRefinedReferenceSpatialMass (τ := τ) (ξ := ξ) (W := W)
        B U b hR hσ S x jetRows X modulus s hA q reference residue hb o bW d N base cells
        (physicalCubeEuclideanSample U d p hm) Z ≤ Real.exp (coefficientErrorVolumeLog Pbound + 4) := by
  obtain ⟨K, hK, htail⟩ := exists_allocated_reference_error_window_bound m dim
  refine ⟨K, hK, ?_⟩
  intro G _ _ I _ n B _ J _ U b R σ hR hσ S x _ hb o Q _ bW d _ C V hC hV ν _ _
    modulus _ hperiod X _ _ q hq reference N hN W τ ξ ρ hW hτ hξ hξ1 hρ hsizeSp hρ8 hρshift
    base cells hmass p hp hm P Rrank ε hP hX hdim hτP hstride hε hεP hsize hrank hRank
    η δf L hδf hL hamb hδL A hLip hfreqP hcoeffP hRefined instRefined
    s hA residue hlengths href hr _ _ _ Cinv hCinv hchart hsmall μ _ _ g hg hg0 hlaw hprojected
    M hM selection hx hdimc hσ1 Pc Ec Tc hPc hEc hTc hη hη1 hMP hRP hRi hσi hcount hηE
    hlarge hi hbound Z hZ Vsp Merr
  have herr := htail B U b hR hσ S x hb o bW d C V hC hV ν modulus hperiod q hq reference
    N hN hW hτ hξ hξ1 hρ hsizeSp hρ8 hρshift base cells hmass p hp hm
    hP hX hdim hτP hstride hε hεP hsize hrank hRank η hδf hL hamb hδL hLip hfreqP hcoeffP
  have hraw := allocatedRefinedReferenceSpatialMass_of_fixed_pivots B U b hR hσ S x jetRows X hM selection hx
    modulus s hA q reference residue hb o bW d g N hN hW hτ hξ base cells hmass
    (physicalCubeEuclideanSample U d p hm) Z hσ1 Cinv hCinv hchart hsmall μ ν hg hg0 hlaw
    (η : ℝ) (Vsp * (Merr + 2 * δf + ε)) hdimc (fun _ => Subtype.val_injective)
    (fun _ z => z.property) hPc hEc hTc hη hη1 hMP hRP hRi hσi hcount hηE hlarge hi hbound
    hq hZ hRefined hlengths href hperiod hr hprojected herr
  refine ⟨hraw, ?_⟩
  intro Pbound D hPbound hdimBound hXbound hD hWD hZi herror
  have hprofile := smoothProbabilityProfile_pos_zero
  have hVsp : 0 ≤ Vsp := by dsimp only [Vsp]; positivity
  apply referenceProxyMass_exp_bound dim X hPbound hdimBound hXbound
    (by exact_mod_cast S.positive) hW hD hWD hZ hZi hraw
  simpa only [mul_one] using mul_le_mul_of_nonneg_left herror hVsp

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable (m dim : ℕ)

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) ((j : ℕ) + 1))
local notation "jetRows" => (fun j : Fin m => (Subtype.val : BoundedBooleanJet (Fin dim) ((j : ℕ) + 1) → Finset (Fin dim)))

theorem exists_allocated_primitive_reference_mass_bound :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ {G : Type*} [Fintype G] [DecidableEq G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale (G := G) B U b R σ) (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (d : ℕ) [NeZero d] (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (modulus : ℕ) [NeZero modulus]
    (_hperiod : ∀ j, integerScalarLattice (jets j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (jetRows j)).mulVecLin.range)
    {X : Type*} [Fintype X] [DecidableEq X]
    (q : X → ℕ) (_hq : ∀ t, 0 < q t)
    (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
      (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
      PrincipalAxisTuples (α := Fin dim) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
    (N : X → ℕ) (_hN : ∀ t, 0 < N t)
    {W τ ξ ρ : ℝ} (_hW : 0 ≤ W) (_hτ : 0 < τ) (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hρ : 0 < ρ)
    (_hsizeSp : ∀ t, 8 * (1 + W) * (q t : ℝ) * ρ ≤ (ξ * τ) * (N t : ℝ))
    (_hρ8 : 8 * (probabilityProfileLipschitz : ℝ) ≤ ρ)
    (_hρshift : 2 * (Fintype.card (Option (LayerSamplerVariables G I n B)) *
      (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0))) ≤ ρ)
    (base : X → ℤ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
    (_hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells
      (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j)
    {P Rrank ε : ℝ} (_hP : 0 ≤ P) (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ P)
    (_hτP : 1 / τ ≤ Real.exp P) (_hstride : ∀ t, (q t : ℝ) ≤ Real.exp P)
    (_hε : 0 < ε) (_hεP : 1 / ε ≤ Real.exp P)
    (_hsize : ∀ t, Real.exp ((P + K) ^ K) ≤ (N t : ℝ))
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) Rrank (U j) (p j))
    (_hRank : Real.exp ((P + K) ^ K) ≤ Rrank)
    {M : ℕ} (_hM : 0 < M) (selection : Fin dim ↪ G)
    (_hx : GoodScalarKernelTuple selection (1/(M : ℝ)) M x)
    (_hdimc : Fintype.card (Fin dim) ≤ m+1) (_hmod : modulus ≤ M ^ (m+1))
    {Perr : ℝ} (_hPerr : 0 ≤ Perr)
    (_hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Perr)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ Perr) (_hn : ∀ j, (n j : ℝ) ≤ Perr)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ Perr)
    (_hMPerr : (M : ℝ) ≤ Real.exp Perr) (_hSP : (S.value : ℝ) ≤ Real.exp Perr)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp Perr) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp Perr)
    (_hBudget : allocatedErrorFourierOutput m Perr ≤ P)
    (η : ℝ≥0) (_hη1NN : η ≤ 1) {δf : ℝ} (_hδf : 0 < δf) (_hδfP : δf⁻¹ ≤ Real.exp Perr),
    let A := Real.toNNReal (coefficientDeckPeriodCap jets Q modulus)
    ∀ (hRefined : 0 < residueRefinedPeriod modulus q),
    let _ : NeZero (residueRefinedPeriod modulus q) := ⟨hRefined.ne'⟩
    ∀ (s : ∀ j, jets j ↪ BoundedIntegerExponent G (j.val+1))
    (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (jetRows j)).submatrix id (s j)).det ≠ 0)
    (residue : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
      (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
      ∀ j, Matrix (jets j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    (hlengths : ∀ t, (Fintype.card (Fin dim)+1)*residueRefinedPeriod modulus q ≤
      principalAxisLength (fun a => ¬allocatedGridAxis (I := I) U b S.value a) (allocatedPrincipalSides B U b S) t)
    (_href : ∀ u r, principalResidueLabel (residueRefinedPeriod modulus q) (reference u r) = r)
    (_hr : ∀ u r v,
      (allocatedLongResidueWeights B U b S (residueRefinedPeriod modulus q) hRefined r hlengths).weight v ≠ 0 → ∀ j,
      integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u jetRows j v) modulus = residue u r j)
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cinv j * ‖v‖)
    (_hsmall : ∀ j, R j ≤ allocatedPhysicalChartRadius (G := G) B (Fin dim) Cinv 1 j)
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (g : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S) →
      EuclideanJetLayers U jets → ℝ)
    (_hg : ∀ y, Continuous (g y)) (_hg0 : ∀ y z, 0 ≤ g y z)
    (_hlaw : ∀ y, (realDensityMeasure μ (fun z => allocatedCoefficientDensity B U b hb o hR hσ S
        (quotientIntegerCover (coefficientIntegerLattice (K := LayerSamplerVariables G I n B) U) d z))).map
      (euclideanCoefficientJetMap U (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
        (allocatedPhysicalCubeDirections B U b S x y) jetRows) =
      realDensityMeasure (Measure.pi (fun j => Measure.pi (fun _ : jets j => ν j))) (g y))
    (_hprojected : ∀ y y₀ (a : ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q),
      (∑ v ∈ spatialWindow (trimmedSpatialRootScale τ N q) 4,
        g y (physicalCubeEuclideanSample U d p hm (physicalResidueReconstruction
          (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y₀)
          (allocatedPhysicalCubeDirections B U b S x y₀) base
          (boundedColumnResidueRepresentative q a) q v))) ≤
        (4 * (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X)) *
          (∏ t, ∏ _i : Unit ⊕ Fin dim, trimmedSpatialRootScale τ N q t))
    (_hσ1 : ∀ j, σ j ≤ 1)
    {Pc Ec Tc : ℝ} (_hPc : 0 ≤ Pc) (_hEc : 0 ≤ Ec) (_hTc : 0 ≤ Tc)
    (_hη : 0 < (η : ℝ))
    (_hMP : (M : ℝ) ≤ Real.exp Pc) (_hRP : ∀ j, R j ≤ Real.exp Pc)
    (_hRi : ∀ j, (R j)⁻¹ ≤ Real.exp Pc) (_hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp Pc)
    (_hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ)+1 ≤ Real.exp Pc)
    (_hηE : (η : ℝ)⁻¹ ≤ Real.exp Ec)
    (_hlarge : Real.exp (allocatedRefinedJointLengthLog (G := G) B (Fin dim) jets Pc Ec Tc) ≤ S.value)
    (_hi : ∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val+1) (jetRows j) (s j) (hA j) (1/(M : ℝ)))
    (_hbound : (residueRefinedPeriod modulus q : ℝ) ≤ Real.exp Tc)
    {Z : ℝ} (_hZ : 0 < Z),
    let Vsp := (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
      (((1 + W) / S.value) ^ dim) ^ Fintype.card X
    let Merr := (η : ℝ) * A *
      (2 * (∑ j, (C j : ℝ) * ((Fintype.card (J j) : ℝ) + 1)) + 1) ^
        Fintype.card (Σ a : LayerSamplerAxis I n, jets a.1)
    allocatedRefinedReferenceSpatialMass (τ := τ) (ξ := ξ) (W := W)
      B U b hR hσ S x jetRows X modulus s hA q reference residue hb o bW d N base cells
      (physicalCubeEuclideanSample U d p hm) Z ≤
      (coarseReferenceMassConstant dim X W S.value + Vsp * (Merr + 2 * δf + ε)) / Z ∧
    ∀ {Pbound D : ℝ}, 0 ≤ Pbound → ((dim + 1 : ℕ) : ℝ) ≤ Pbound →
      (Fintype.card X : ℝ) ≤ Pbound → D ≤ Real.exp Pbound → W ≤ D * S.value →
      Z⁻¹ ≤ 2 → Merr + 2 * δf + ε ≤ 1 →
      allocatedRefinedReferenceSpatialMass (τ := τ) (ξ := ξ) (W := W)
        B U b hR hσ S x jetRows X modulus s hA q reference residue hb o bW d N base cells
        (physicalCubeEuclideanSample U d p hm) Z ≤ Real.exp (coefficientErrorVolumeLog Pbound + 4) := by
  obtain ⟨K, hK, htest⟩ := exists_allocated_fixed_reference_mass_bound m dim
  refine ⟨K, hK, ?_⟩
  intro G _ _ I _ n B _ J _ U b R σ hR hσ S x _ hb o Q _ bW d _ C V hC hV ν _ _
    modulus _ hperiod X _ _ q hq reference N hN W τ ξ ρ hW hτ hξ hξ1 hρ hsizeSp hρ8 hρshift
    base cells hmass p hp hm P Rrank ε hP hX hdim hτP hstride hε hεP hsize hrank hRank
    M hM selection hx hdimc hmod Perr hPerr hvars hI hn hJ hMPerr hSP hCP hVP hBudget
    η hη1NN δf hδf hδfP A hRefined instRefined
    s hA residue hlengths href hr _ _ _ Cinv hCinv hchart hsmall μ _ _ g hg hg0 hlaw hprojected
    hσ1 Pc Ec Tc hPc hEc hTc hη hMP hRP hRi hσi hcount hηE hlarge hi hbound Z hZ
  obtain ⟨hL, _hp, hamb, hδL, hLip, hfreq, hcoeff⟩ :=
    allocatedErrorPrimitive_fourier_budget B U b S jetRows hdimc (fun _ => Subtype.val_injective)
      hb bW M modulus hmod η C V hPerr hvars hI hn hJ hη1NN hMPerr hSP hCP hVP hδfP
  exact htest B U b hR hσ S x hb o bW d C V hC hV ν modulus hperiod q hq reference
    N hN hW hτ hξ hξ1 hρ hsizeSp hρ8 hρshift base cells hmass p hp hm
    hP hX hdim hτP hstride hε hεP hsize hrank hRank η hδf hL hamb hδL hLip
    (hfreq.trans (Real.exp_le_exp.mpr hBudget)) (hcoeff.trans (Real.exp_le_exp.mpr hBudget))
    hRefined s hA residue hlengths href hr Cinv hCinv hchart hsmall μ g hg hg0 hlaw hprojected
    hM selection hx hdimc hσ1 hPc hEc hTc hη hη1NN hMP hRP hRi hσi hcount hηE hlarge hi hbound hZ

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable (m dim : ℕ)

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) ((j : ℕ) + 1))
local notation "jetRows" => (fun j : Fin m => (Subtype.val : BoundedBooleanJet (Fin dim) ((j : ℕ) + 1) → Finset (Fin dim)))

theorem exists_allocated_certified_reference_mass_bound :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ {G : Type*} [Fintype G] [DecidableEq G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale (G := G) B U b R σ) (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (d : ℕ) [NeZero d] (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (modulus : ℕ) [NeZero modulus]
    (_hperiod : ∀ j, integerScalarLattice (jets j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (jetRows j)).mulVecLin.range)
    {X : Type*} [Fintype X] [DecidableEq X]
    (q : X → ℕ) (_hq : ∀ t, 0 < q t)
    (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
      (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
      PrincipalAxisTuples (α := Fin dim) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
    (N : X → ℕ) (_hN : ∀ t, 0 < N t)
    {W τ ξ ρ : ℝ} (_hW : 0 ≤ W) (_hτ : 0 < τ) (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hρ : 0 < ρ)
    (_hsizeSp : ∀ t, 8 * (1 + W) * (q t : ℝ) * ρ ≤ (ξ * τ) * (N t : ℝ))
    (_hρ8 : 8 * (probabilityProfileLipschitz : ℝ) ≤ ρ)
    (_hρshift : 2 * (Fintype.card (Option (LayerSamplerVariables G I n B)) *
      (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0))) ≤ ρ)
    (base : X → ℤ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
    (_hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells
      (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j)
    {P Rrank ε : ℝ} (_hP : 0 ≤ P) (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ P)
    (_hτP : 1 / τ ≤ Real.exp P) (_hstride : ∀ t, (q t : ℝ) ≤ Real.exp P)
    (_hε : 0 < ε) (_hεP : 1 / ε ≤ Real.exp P)
    (_hsize : ∀ t, Real.exp ((P + K) ^ K) ≤ (N t : ℝ))
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) Rrank (U j) (p j))
    (_hRank : Real.exp ((P + K) ^ K) ≤ Rrank)
    {M : ℕ} (_hM : 0 < M) (selection : Fin dim ↪ G)
    (_hx : GoodScalarKernelTuple selection (1/(M : ℝ)) M x)
    (_hdimc : Fintype.card (Fin dim) ≤ m+1) (_hmod : modulus ≤ M ^ (m+1))
    {Perr : ℝ} (_hPerr : 0 ≤ Perr)
    (_hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Perr)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ Perr) (_hn : ∀ j, (n j : ℝ) ≤ Perr)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ Perr)
    (_hMPerr : (M : ℝ) ≤ Real.exp Perr) (_hSP : (S.value : ℝ) ≤ Real.exp Perr)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp Perr) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp Perr)
    (_hBudget : allocatedErrorFourierOutput m Perr ≤ P)
    (η : ℝ≥0) (_hη1NN : η ≤ 1) {δf : ℝ} (_hδf : 0 < δf) (_hδfP : δf⁻¹ ≤ Real.exp Perr),
    let A := Real.toNNReal (coefficientDeckPeriodCap jets Q modulus)
    ∀ (hRefined : 0 < residueRefinedPeriod modulus q),
    let _ : NeZero (residueRefinedPeriod modulus q) := ⟨hRefined.ne'⟩
    ∀ (s : ∀ j, jets j ↪ BoundedIntegerExponent G (j.val+1))
    (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (jetRows j)).submatrix id (s j)).det ≠ 0)
    (residue : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
      (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
      ∀ j, Matrix (jets j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    (hlengths : ∀ t, (Fintype.card (Fin dim)+1)*residueRefinedPeriod modulus q ≤
      principalAxisLength (fun a => ¬allocatedGridAxis (I := I) U b S.value a) (allocatedPrincipalSides B U b S) t)
    (_href : ∀ u r, principalResidueLabel (residueRefinedPeriod modulus q) (reference u r) = r)
    (_hr : ∀ u r v,
      (allocatedLongResidueWeights B U b S (residueRefinedPeriod modulus q) hRefined r hlengths).weight v ≠ 0 → ∀ j,
      integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u jetRows j v) modulus = residue u r j)
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cinv j * ‖v‖)
    (_hsmall : ∀ j, R j ≤ allocatedPhysicalChartRadius (G := G) B (Fin dim) Cinv 1 j)
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (g : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S) →
      EuclideanJetLayers U jets → ℝ)
    (_hg : ∀ y, Continuous (g y)) (_hg0 : ∀ y z, 0 ≤ g y z)
    (_hlaw : ∀ y, (realDensityMeasure μ (fun z => allocatedCoefficientDensity B U b hb o hR hσ S
        (quotientIntegerCover (coefficientIntegerLattice (K := LayerSamplerVariables G I n B) U) d z))).map
      (euclideanCoefficientJetMap U (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
        (allocatedPhysicalCubeDirections B U b S x y) jetRows) =
      realDensityMeasure (Measure.pi (fun j => Measure.pi (fun _ : jets j => ν j))) (g y))
    (_hgi : ∀ y, Integrable (g y) (Measure.pi (fun j => Measure.pi (fun _ : jets j => ν j))))
    (_hgm : ∀ y, (∫ z, g y z ∂(Measure.pi (fun j => Measure.pi (fun _ : jets j => ν j)))) = 1)
    (Afourier : ℕ) {Pfourier : ℝ} (_hPfourier : 0 ≤ Pfourier)
    (_hFourier : allocatedProjectedFourierData B U b S C V d g Afourier Pfourier)
    (_hmf : (m : ℝ) ≤ Pfourier)
    (_hvarsf : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pfourier)
    (_hRif : ∀ j, (R j)⁻¹ ≤ Real.exp Pfourier) (_hσif : ∀ j, (σ j)⁻¹ ≤ Real.exp Pfourier)
    (_hcountf : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) ≤ Pfourier)
    (_hIf : ∀ j, (Fintype.card (I j) : ℝ) ≤ Pfourier) (_hnf : ∀ j, (n j : ℝ) ≤ Pfourier)
    (_hJf : ∀ j, (Fintype.card (J j) : ℝ) ≤ Pfourier)
    (_hAPf : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Pfourier)
    (_hCPf : ∀ j, (C j : ℝ) ≤ Real.exp Pfourier) (_hVPf : ∀ j, (V j : ℝ) ≤ Real.exp Pfourier)
    (_hFourierBudget : allocatedJetFourierBudget m dim Afourier Pfourier ≤ P)
    (_hσ1 : ∀ j, σ j ≤ 1)
    {Pc Ec Tc : ℝ} (_hPc : 0 ≤ Pc) (_hEc : 0 ≤ Ec) (_hTc : 0 ≤ Tc)
    (_hη : 0 < (η : ℝ))
    (_hMP : (M : ℝ) ≤ Real.exp Pc) (_hRP : ∀ j, R j ≤ Real.exp Pc)
    (_hRi : ∀ j, (R j)⁻¹ ≤ Real.exp Pc) (_hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp Pc)
    (_hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ)+1 ≤ Real.exp Pc)
    (_hηE : (η : ℝ)⁻¹ ≤ Real.exp Ec)
    (_hlarge : Real.exp (allocatedRefinedJointLengthLog (G := G) B (Fin dim) jets Pc Ec Tc) ≤ S.value)
    (_hi : ∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val+1) (jetRows j) (s j) (hA j) (1/(M : ℝ)))
    (_hbound : (residueRefinedPeriod modulus q : ℝ) ≤ Real.exp Tc)
    {Z : ℝ} (_hZ : 0 < Z),
    let Vsp := (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
      (((1 + W) / S.value) ^ dim) ^ Fintype.card X
    let Merr := (η : ℝ) * A *
      (2 * (∑ j, (C j : ℝ) * ((Fintype.card (J j) : ℝ) + 1)) + 1) ^
        Fintype.card (Σ a : LayerSamplerAxis I n, jets a.1)
    allocatedRefinedReferenceSpatialMass (τ := τ) (ξ := ξ) (W := W)
      B U b hR hσ S x jetRows X modulus s hA q reference residue hb o bW d N base cells
      (physicalCubeEuclideanSample U d p hm) Z ≤
      (coarseReferenceMassConstant dim X W S.value + Vsp * (Merr + 2 * δf + ε)) / Z ∧
    ∀ {Pbound D : ℝ}, 0 ≤ Pbound → ((dim + 1 : ℕ) : ℝ) ≤ Pbound →
      (Fintype.card X : ℝ) ≤ Pbound → D ≤ Real.exp Pbound → W ≤ D * S.value →
      Z⁻¹ ≤ 2 → Merr + 2 * δf + ε ≤ 1 →
      allocatedRefinedReferenceSpatialMass (τ := τ) (ξ := ξ) (W := W)
        B U b hR hσ S x jetRows X modulus s hA q reference residue hb o bW d N base cells
        (physicalCubeEuclideanSample U d p hm) Z ≤ Real.exp (coefficientErrorVolumeLog Pbound + 4) := by
  obtain ⟨K, hK, hmassBound⟩ := exists_allocated_primitive_reference_mass_bound m dim
  obtain ⟨T, hT, hproject⟩ := exists_allocated_retained_reference_mass m dim
  refine ⟨max K T, hK.trans (le_max_left _ _), ?_⟩
  intro G _ _ I _ n B _ J _ U b R σ hR hσ S x _ hb o Q _ bW d _ C V hC hV ν _ _
    modulus _ hperiod X _ _ q hq reference N hN W τ ξ ρ hW hτ hξ hξ1 hρ hsizeSp hρ8 hρshift
    base cells hmass p hp hm P Rrank ε hP hX hdim hτP hstride hε hεP hsize hrank hRank
    M hM selection hx hdimc hmod Perr hPerr hvars hI hn hJ hMPerr hSP hCP hVP hBudget
    η hη1NN δf hδf hδfP A hRefined instRefined
    s hA residue hlengths href hr _ _ _ Cinv hCinv hchart hsmall μ _ _ g hg hg0 hlaw
    hgi hgm Afourier Pfourier hPfourier hFourier hmf hvarsf hRif hσif hcountf hIf hnf hJf hAPf hCPf hVPf hFourierBudget
    hσ1 Pc Ec Tc hPc hEc hTc hη hMP hRP hRi hσi hcount hηE hlarge hi hbound Z hZ
  have hKcut : Real.exp ((P + K)^K) ≤ Real.exp ((P + (max K T : ℕ))^max K T) :=
    Real.exp_le_exp.mpr (shifted_power_self_mono hP (by omega) (le_max_left _ _))
  have hTcut : Real.exp ((P + T)^T) ≤ Real.exp ((P + (max K T : ℕ))^max K T) :=
    Real.exp_le_exp.mpr (shifted_power_self_mono hP (by omega) (le_max_right _ _))
  have hprojected := hproject B U b S (fun _ => 0) x C V d (NeZero.pos d) g ν hg0 hgi hgm
    Afourier hPfourier hFourier hmf hvarsf hRif hσif hcountf hIf hnf hJf hAPf hCPf hVPf
    hFourierBudget hX hdim p hp hm N q hq hW hτ hξ1 hρ hτP hstride
    (fun t => hTcut.trans (hsize t)) hrank (hTcut.trans hRank) hsizeSp hρ8 hρshift
  exact hmassBound B U b hR hσ S x hb o bW d C V hC hV ν modulus hperiod q hq reference
    N hN hW hτ hξ hξ1 hρ hsizeSp hρ8 hρshift base cells hmass p hp hm
    hP hX hdim hτP hstride hε hεP (fun t => hKcut.trans (hsize t)) hrank (hKcut.trans hRank)
    hM selection hx hdimc hmod hPerr hvars hI hn hJ hMPerr hSP hCP hVP hBudget η hη1NN hδf hδfP
    hRefined s hA residue hlengths href hr Cinv hCinv hchart hsmall μ g hg hg0 hlaw
    (fun y y₀ a => hprojected y y₀ base a)
    hσ1 hPc hEc hTc hη hMP hRP hRi hσi hcount hηE hlarge hi hbound hZ

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable (m dim : ℕ)

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) ((j : ℕ) + 1))
local notation "jetRows" => (fun j : Fin m => (Subtype.val : BoundedBooleanJet (Fin dim) ((j : ℕ) + 1) → Finset (Fin dim)))

theorem exists_allocated_accuracy_reference_mass_bound :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ {G : Type*} [Fintype G] [DecidableEq G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale (G := G) B U b R σ) (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (d : ℕ) [NeZero d] (C V : Fin m → ℝ≥0)
    (Afourier : ℕ) {P pB E : ℝ} (_hP : 0 ≤ P) (_hpB : 0 ≤ pB) (_hE : 0 ≤ E)
    (_hpP : pB ≤ P) (_hSP : (S.value : ℝ) ≤ Real.exp P)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (modulus : ℕ) [NeZero modulus]
    (_hperiod : ∀ j, integerScalarLattice (jets j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (jetRows j)).mulVecLin.range)
    {X : Type*} [Fintype X] [DecidableEq X]
    (q : X → ℕ) (_hq : ∀ t, 0 < q t)
    (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
      (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
      PrincipalAxisTuples (α := Fin dim) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
    (N : X → ℕ) (_hN : ∀ t, 0 < N t)
    {W τ ξ ρ : ℝ} (_hW : 0 ≤ W) (_hτ : 0 < τ) (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hρ : 0 < ρ)
    (_hsizeSp : ∀ t, 8 * (1 + W) * (q t : ℝ) * ρ ≤ (ξ * τ) * (N t : ℝ))
    (_hρ8 : 8 * (probabilityProfileLipschitz : ℝ) ≤ ρ)
    (_hρshift : 2 * (Fintype.card (Option (LayerSamplerVariables G I n B)) *
      (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0))) ≤ ρ)
    (base : X → ℤ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
    (_hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells
      (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j)
    {Rrank : ℝ}
    (_hτP : 1 / τ ≤ Real.exp (allocatedUnifiedSamplingBudget m dim Afourier P pB E)) (_hstride : ∀ t, (q t : ℝ) ≤ Real.exp (allocatedUnifiedSamplingBudget m dim Afourier P pB E))
    (_hsize : ∀ t, Real.exp (((allocatedUnifiedSamplingBudget m dim Afourier P pB E) + K)^K) ≤ (N t : ℝ))
    (_hrank : ∀ j, HasLayerSamplingRank (j.val+1) (fun t => (N t : ℝ)) Rrank (U j) (p j))
    (_hRank : Real.exp (((allocatedUnifiedSamplingBudget m dim Afourier P pB E) + K)^K) ≤ Rrank)
    {M : ℕ} (_hM : 0 < M) (selection : Fin dim ↪ G)
    (_hx : GoodScalarKernelTuple selection (1/(M : ℝ)) M x)
    (_hdimc : Fintype.card (Fin dim) ≤ m+1) (_hmod : modulus ≤ M ^ (m+1))
    (_hdimB : ((dim+1 : ℕ) : ℝ) ≤ pB)
    (_hvarsB : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ pB)
    (_hIB : ∀ j, (Fintype.card (I j) : ℝ) ≤ pB) (_hnB : ∀ j, (n j : ℝ) ≤ pB)
    (_hJB : ∀ j, (Fintype.card (J j) : ℝ) ≤ pB) (_hXB : (Fintype.card X : ℝ) ≤ pB)
    (_hMPB : (M : ℝ) ≤ Real.exp pB) (_hCPB : ∀ j, (C j : ℝ) ≤ Real.exp pB),
    ∀ (hRefined : 0 < residueRefinedPeriod modulus q),
    let _ : NeZero (residueRefinedPeriod modulus q) := ⟨hRefined.ne'⟩
    ∀ (s : ∀ j, jets j ↪ BoundedIntegerExponent G (j.val+1))
    (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (jetRows j)).submatrix id (s j)).det ≠ 0)
    (residue : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
      (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
      ∀ j, Matrix (jets j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    (hlengths : ∀ t, (Fintype.card (Fin dim)+1)*residueRefinedPeriod modulus q ≤
      principalAxisLength (fun a => ¬allocatedGridAxis (I := I) U b S.value a) (allocatedPrincipalSides B U b S) t)
    (_href : ∀ u r, principalResidueLabel (residueRefinedPeriod modulus q) (reference u r) = r)
    (_hr : ∀ u r v,
      (allocatedLongResidueWeights B U b S (residueRefinedPeriod modulus q) hRefined r hlengths).weight v ≠ 0 → ∀ j,
      integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u jetRows j v) modulus = residue u r j)
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cinv j * ‖v‖)
    (_hsmall : ∀ j, R j ≤ allocatedPhysicalChartRadius (G := G) B (Fin dim) Cinv 1 j)
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (g : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S) →
      EuclideanJetLayers U jets → ℝ)
    (_hg : ∀ y, Continuous (g y)) (_hg0 : ∀ y z, 0 ≤ g y z)
    (_hlaw : ∀ y, (realDensityMeasure μ (fun z => allocatedCoefficientDensity B U b hb o hR hσ S
        (quotientIntegerCover (coefficientIntegerLattice (K := LayerSamplerVariables G I n B) U) d z))).map
      (euclideanCoefficientJetMap U (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
        (allocatedPhysicalCubeDirections B U b S x y) jetRows) =
      realDensityMeasure (Measure.pi (fun j => Measure.pi (fun _ : jets j => ν j))) (g y))
    (_hgi : ∀ y, Integrable (g y) (Measure.pi (fun j => Measure.pi (fun _ : jets j => ν j))))
    (_hgm : ∀ y, (∫ z, g y z ∂(Measure.pi (fun j => Measure.pi (fun _ : jets j => ν j)))) = 1)
    (_hFourier : allocatedProjectedFourierData B U b S C V d g Afourier P)
    (_hmf : (m : ℝ) ≤ P)
    (_hvarsf : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hRif : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσif : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (_hcountf : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) ≤ P)
    (_hIf : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hnf : ∀ j, (n j : ℝ) ≤ P)
    (_hJf : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAPf : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (_hCPf : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVPf : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (_hσ1 : ∀ j, σ j ≤ 1)
    {Pc Tc : ℝ} (_hPc : 0 ≤ Pc) (_hTc : 0 ≤ Tc)
    (_hMP : (M : ℝ) ≤ Real.exp Pc) (_hRP : ∀ j, R j ≤ Real.exp Pc)
    (_hRi : ∀ j, (R j)⁻¹ ≤ Real.exp Pc) (_hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp Pc)
    (_hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ)+1 ≤ Real.exp Pc)
    (_hlarge : Real.exp (allocatedRefinedJointLengthLog (G := G) B (Fin dim) jets Pc (allocatedCoefficientAccuracyLog m pB (E+3)) Tc) ≤ S.value)
    (_hi : ∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val+1) (jetRows j) (s j) (hA j) (1/(M : ℝ)))
    (_hbound : (residueRefinedPeriod modulus q : ℝ) ≤ Real.exp Tc)
    {Z D : ℝ} (_hZ : 0 < Z) (_hZi : Z⁻¹ ≤ 2)
    (_hD : D ≤ Real.exp pB) (_hWD : W ≤ D * S.value),
    allocatedRefinedReferenceSpatialMass (τ := τ) (ξ := ξ) (W := W)
      B U b hR hσ S x jetRows X modulus s hA q reference residue hb o bW d N base cells
      (physicalCubeEuclideanSample U d p hm) Z ≤ Real.exp (coefficientErrorVolumeLog pB + 4) := by
  obtain ⟨K, hK, hcertified⟩ := exists_allocated_certified_reference_mass_bound m dim
  refine ⟨K, hK, ?_⟩
  intro G _ _ I _ n B _ J _ U b R σ hR hσ S x _ hb o Q _ bW d _ C V
    Afourier P pB E hP hpB hE hpP hSP hC hV ν _ _
    modulus _ hperiod X _ _ q hq reference N hN W τ ξ ρ hW hτ hξ hξ1 hρ hsizeSp hρ8 hρshift
    base cells hmass poly hpoly hm Rrank hτP hstride hsize hrank hRank
    M hM selection hx hdimc hmod hdimB hvarsB hIB hnB hJB hXB hMPB hCPB
    hRefined instRefined s hA residue hlengths href hr _ _ _ Cinv hCinv hchart hsmall μ _ _ g hg hg0 hlaw
    hgi hgm hFourier hmf hvarsf hRif hσif hcountf hIf hnf hJf hAPf hCPf hVPf
    hσ1 Pc Tc hPc hTc hMP hRP hRi hσi hcount hlarge hi hbound Z D hZ hZi hD hWD
  let Pmass := allocatedUnifiedSamplingBudget m dim Afourier P pB E
  let Perr := allocatedTupleErrorBudget m P pB E
  let a := allocatedCoefficientAccuracy m pB (E+3)
  have hE3 : 0 ≤ E+3 := by linarith
  have ha := allocatedCoefficientAccuracy_bounds m hpB hE3
  obtain ⟨hPerr, hPPerr, hAccuracy, hPmass, hScalar, _hWidth, _hPplus, hpMass, _hEMass, hDimMass⟩ :=
    allocatedUnifiedSamplingBudget_bounds m dim Afourier hP hpB hE
  have hs := allocatedScalarSamplingBudget_bounds m dim Afourier hP hPerr
  have hPerrMass : Perr ≤ Pmass := hs.2.2.2.trans hScalar
  have hFourierBudget := hs.2.1.trans hScalar
  have hErrorBudget := hs.2.2.1.trans hScalar
  have hpErr : pB ≤ Perr := hpP.trans hPPerr
  have hainvErr : a⁻¹ ≤ Real.exp Perr := ha.2.2.le.trans (Real.exp_le_exp.mpr hAccuracy)
  have hainvMass : 1/a ≤ Real.exp Pmass := by
    simpa only [one_div] using hainvErr.trans (Real.exp_le_exp.mpr hPerrMass)
  have hlog : 0 ≤ allocatedCoefficientAccuracyLog m pB (E+3) :=
    neg_nonpos.mp (Real.exp_le_one_iff.mp ha.2.1)
  have hXmass : (Fintype.card X : ℝ) ≤ Pmass := hXB.trans hpMass
  have hdimMass : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ Pmass := by
    apply le_trans _ hDimMass
    have hd : (dim : ℝ)+1 ≤ pB := by exact_mod_cast hdimB
    simp only [Fintype.card_prod, Fintype.card_option, Fintype.card_fin, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one]
    have hh := mul_le_mul hd hXB (Nat.cast_nonneg (Fintype.card X)) hpB
    exact hh.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) hpB)
  let η : ℝ≥0 := ⟨a, ha.1.le⟩
  have hresult := hcertified B U b hR hσ S x hb o bW d C V hC hV ν modulus hperiod q hq reference
    N hN hW hτ hξ hξ1 hρ hsizeSp hρ8 hρshift base cells hmass poly hpoly hm
    hPmass hXmass hdimMass hτP hstride ha.1 hainvMass hsize hrank hRank
    hM selection hx hdimc hmod hPerr
    (hvarsB.trans hpErr) (fun j => (hIB j).trans hpErr) (fun j => (hnB j).trans hpErr)
    (fun j => (hJB j).trans hpErr) (hMPB.trans (Real.exp_le_exp.mpr hpErr))
    (hSP.trans (Real.exp_le_exp.mpr hPPerr))
    (fun j => (hCPB j).trans (Real.exp_le_exp.mpr hpErr))
    (fun j => (hVPf j).trans (Real.exp_le_exp.mpr hPPerr)) hErrorBudget η ha.2.1 ha.1 hainvErr
    hRefined s hA residue hlengths href hr Cinv hCinv hchart hsmall μ g hg hg0 hlaw
    hgi hgm Afourier hP hFourier hmf hvarsf hRif hσif hcountf hIf hnf hJf hAPf hCPf hVPf hFourierBudget
    hσ1 hPc hlog hTc ha.1 hMP hRP hRi hσi hcount ha.2.2.le hlarge hi hbound hZ
  apply hresult.2 hpB hdimB hXB hD hWD hZi
  have herror := allocatedCoefficientAccuracy_proxy_error B U b hb bW jetRows
    (by simpa only [Fintype.card_fin] using hdimc) (fun _ => Subtype.val_injective) C hpB hE3
    hvarsB hIB hnB hJB hCPB hMPB hmod
  have herrorOne := herror.trans (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hE3))
  rw [Real.coe_toNNReal _ (coefficientDeckPeriodCap_nonneg jets Q modulus)]
  change a * coefficientDeckPeriodCap jets Q modulus *
      (2 * (∑ j, (C j : ℝ) * ((Fintype.card (J j) : ℝ) + 1)) + 1) ^
        Fintype.card (Σ ax : LayerSamplerAxis I n, jets ax.1) + 2 * a + a ≤ 1
  simpa only [mul_assoc] using herrorOne

end Erdos3.VectorPolynomial

end

end OAI
