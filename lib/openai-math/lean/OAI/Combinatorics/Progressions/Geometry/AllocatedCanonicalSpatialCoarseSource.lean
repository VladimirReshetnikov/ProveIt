import OAI.Combinatorics.Progressions.Estimates.AllocatedCanonicalUniformCoarseSource

namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (C V : Fin m → ℝ≥0)

theorem AllocatedSourceNumerics.canonical_spatial_size
    {P : ℝ} (hnum : AllocatedSourceNumerics B U b S C V P)
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    {X : Type*} [Fintype X] {dim M : ℕ} (selection : Fin dim ↪ G)
    {p target Ecap Qstride Etau : ℝ}
    (hp : 0 ≤ p) (htarget : 0 ≤ target)
    (hEcap : 0 ≤ Ecap) (hQstride : 0 ≤ Qstride) (hEtau : 0 ≤ Etau)
    (hM : 0 < M) (hm : ((m + 1 : ℕ) : ℝ) ≤ p)
    (hdim : ((dim + 1 : ℕ) : ℝ) ≤ p)
    (hG : (Fintype.card G : ℝ) ≤ p) (hX : (Fintype.card X : ℝ) ≤ p)
    (hMp : (M : ℝ) ≤ Real.exp p)
    (stride N : X → ℕ) (hstride : ∀ i, (stride i : ℝ) ≤ Real.exp Qstride)
    {τ : ℝ} (hτ : 0 < τ) (hτinv : τ⁻¹ ≤ Real.exp Etau)
    (hside : ∀ i, Real.exp (normalizedTupleSideLog X
      (PrincipalTupleIndex B (layerSamplerDegree I n)) selection p target
      (allocatedSpatialLateLog (G := G) B P P + Ecap + Qstride + Etau)) ≤ (N i : ℝ)) :
    let W := allocatedPhysicalRootBudget B U b S (fun _ => 0)
    let C₀ := 1 + (S.value : ℝ) + W
    let Centry := allocatedPhysicalEntryBudget B U b S (fun _ => 0)
    ∀ i, 8 * (1 + W) * (stride i : ℝ) * normalizedTupleResolution X
      (PrincipalTupleIndex B (layerSamplerDegree I n)) selection M p target
      C₀ W (Real.exp Ecap) Centry ≤
        (normalizedTupleNarrowWidth X (PrincipalTupleIndex B (layerSamplerDegree I n))
          selection M p target * τ) * (N i : ℝ) := by
  intro W C₀ Centry i
  obtain ⟨hW, hl₀, _, hC₀, _, _, hC₀l, _, hCentryl, hWl, hprofile⟩ :=
    hnum.late_bounds B U b S C V hR hσ
  let l := allocatedSpatialLateLog (G := G) B P P + Ecap + Qstride + Etau
  have hl : 0 ≤ l := by dsimp [l]; linarith only [hl₀, hEcap, hQstride, hEtau]
  have hl₀l : allocatedSpatialLateLog (G := G) B P P ≤ l := by
    dsimp [l]; linarith only [hEcap, hQstride, hEtau]
  have hEcapl : Ecap ≤ l := by dsimp [l]; linarith only [hl₀, hQstride, hEtau]
  have hQstridel : Qstride ≤ l := by dsimp [l]; linarith only [hl₀, hEcap, hEtau]
  have hEtaul : Etau ≤ l := by dsimp [l]; linarith only [hl₀, hEcap, hQstride]
  exact normalizedTupleSpatialSize X (PrincipalTupleIndex B (layerSamplerDegree I n))
    (m := m) selection hp htarget hl hM hm hdim hG hX hMp
    (zero_le_one.trans hC₀) hW (Real.exp_pos _).le
    (zero_le_one.trans (allocatedPhysicalEntryBudget_one_le B U b S (fun _ => 0)))
    (hC₀l.trans (Real.exp_le_exp.mpr hl₀l)) (hWl.trans (Real.exp_le_exp.mpr hl₀l))
    (Real.exp_le_exp.mpr hEcapl) (hCentryl.trans (Real.exp_le_exp.mpr hl₀l))
    (hprofile.trans (Real.exp_le_exp.mpr hl₀l)) (Nat.cast_nonneg _)
    ((hstride i).trans (Real.exp_le_exp.mpr hQstridel)) hτ
    (hτinv.trans (Real.exp_le_exp.mpr hEtaul)) (hside i)

theorem AllocatedSourceNumerics.canonical_spatial_choices
    {P : ℝ} (hnum : AllocatedSourceNumerics B U b S C V P)
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    {X : Type*} [Fintype X] {dim M : ℕ} (selection : Fin dim ↪ G)
    {p target Ecap Qstride Etau earlyMesh : ℝ}
    (hp : 0 ≤ p) (htarget : 0 ≤ target)
    (hEcap : 0 ≤ Ecap) (hQstride : 0 ≤ Qstride) (hEtau : 0 ≤ Etau)
    (hM : 0 < M) (hm : ((m + 1 : ℕ) : ℝ) ≤ p)
    (hdim : ((dim + 1 : ℕ) : ℝ) ≤ p)
    (hG : (Fintype.card G : ℝ) ≤ p) (hX : (Fintype.card X : ℝ) ≤ p)
    (hMp : (M : ℝ) ≤ Real.exp p)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Real.exp p)
    (hearlyMesh : 0 < earlyMesh)
    (stride N : X → ℕ) (hstridepos : ∀ i, 0 < stride i)
    (hstride : ∀ i, (stride i : ℝ) ≤ Real.exp Qstride)
    {τ : ℝ} (hτ : 0 < τ) (hτinv : τ⁻¹ ≤ Real.exp Etau)
    (hside : ∀ i, Real.exp (normalizedTupleSideLog X
      (PrincipalTupleIndex B (layerSamplerDegree I n)) selection p target
      (allocatedSpatialLateLog (G := G) B P P + Ecap + Qstride + Etau)) ≤ (N i : ℝ)) :
    let W := allocatedPhysicalRootBudget B U b S (fun _ => 0)
    let C₀ := 1 + (S.value : ℝ) + W
    let Centry := allocatedPhysicalEntryBudget B U b S (fun _ => 0)
    let ξ := normalizedTupleNarrowWidth X (PrincipalTupleIndex B (layerSamplerDegree I n))
      selection M p target
    let δ := normalizedTupleRadius X selection M p target W
    let ρ := normalizedTupleResolution X (PrincipalTupleIndex B (layerSamplerDegree I n))
      selection M p target C₀ W (Real.exp Ecap) Centry
    let mesh := min (δ / 4) earlyMesh
    0 ≤ W ∧ 1 ≤ C₀ ∧ (S.value : ℝ) ≤ C₀ ∧ W ≤ C₀ ∧
    W ≤ Fintype.card (LayerSamplerVariables G I n B) * (S.value : ℝ) ∧
    0 < ξ ∧ ξ ≤ 1 ∧ 0 < δ ∧ δ ≤ 1 ∧ 0 < ρ ∧
    0 < mesh ∧ mesh ≤ earlyMesh ∧ mesh ≤ δ / 4 ∧
    (∀ i, 8 * (1 + W) * (stride i : ℝ) * ρ ≤ (ξ * τ) * (N i : ℝ)) ∧
    anisotropicSpatialMeshThreshold selection (PrincipalTupleIndex B (layerSamplerDegree I n)) C₀ ≤ ρ ∧
    8 * probabilityProfileLipschitz ≤ ρ ∧
    2 * (Fintype.card (Option (LayerSamplerVariables G I n B)) * (2 * Centry)) ≤ ρ ∧
    Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) * (2 * Centry) ≤ δ * ρ ∧
    Real.exp Ecap * (24 * probabilityProfileLipschitz *
      Fintype.card (Option (LayerSamplerVariables G I n B) × X) / ρ) ≤ normalizedSpatialShare target / 2 ∧
    (∀ period : ℕ, period ≤ M ^ (m + 1) →
      allocatedTupleSpatialError (Fintype.card X) selection
        (PrincipalTupleIndex B (layerSamplerDegree I n)) M period C₀ ρ ξ W δ mesh *
        coarseReferenceMassConstant dim X W S.value ≤ normalizedSpatialShare target / 2) ∧
    let widths := narrowTrimmedSpatialWidths (G := G)
      (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    (∀ i, 0 < N i) ∧ (∀ z, 0 < widths z) ∧
    ∀ cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride),
      cells.Nonempty → 0 < ∑' z, selectedResidueSmoothWeight stride cells widths z := by
  intro W C₀ Centry ξ δ ρ mesh
  obtain ⟨hW, _, _, hC₀, hLC, hWC, _⟩ := hnum.late_bounds B U b S C V hR hσ
  have hWscale : W ≤ Fintype.card (LayerSamplerVariables G I n B) * (S.value : ℝ) := by
    simp only [W, allocatedPhysicalRootBudget, Int.cast_zero, abs_zero, Finset.sum_const_zero,
      zero_add, le_refl]
  have hL : (1 : ℝ) ≤ S.value := by exact_mod_cast S.positive
  obtain ⟨hξ, hξ1, _, hchoices⟩ := canonicalSlicedSpatialChoices
    (N := PrincipalTupleIndex B (layerSamplerDegree I n)) (X := X) (m := m)
    selection hM hp htarget hm hdim hG hX hMp
  obtain ⟨hδ, hδ1, hρ, hmesh, hmeshEarly, hmeshFine, hthreshold, hρ8,
    hshift, hmove, hboundary, hsite⟩ :=
    hchoices (C₀ := C₀) (W := W) (L := S.value) (Cg := Real.exp Ecap)
      (Centry := Centry) (growth := Fintype.card (LayerSamplerVariables G I n B))
      (zero_le_one.trans hC₀) hW hL (Real.exp_pos _).le
      (zero_le_one.trans (allocatedPhysicalEntryBudget_one_le B U b S (fun _ => 0)))
      hvars hWscale hearlyMesh
  have hphysical := hnum.canonical_spatial_size B U b S C V hR hσ selection hp htarget
    hEcap hQstride hEtau hM hm hdim hG hX hMp stride N hstride hτ hτinv hside
  have hN (i) : 0 < N i := by
    exact_mod_cast (Real.exp_pos _).trans_le (hside i)
  have hwidth := narrowTrimmedSpatialWidths_pos (G := G)
    (J := PrincipalTupleIndex B (layerSamplerDegree I n)) hW hτ hξ N hN
  refine ⟨hW, hC₀, hLC, hWC, hWscale, hξ, hξ1, hδ, hδ1, hρ,
    hmesh, hmeshEarly, hmeshFine, hphysical, hthreshold, hρ8, ?_, hmove, hboundary, hsite,
    hN, hwidth, ?_⟩
  · simpa only [mul_assoc] using hshift
  · intro cells hcells
    exact (exists_selectedResidue_physical_cap (fun _ : LayerSamplerVariables G I n B => 0)
      stride hstridepos cells hcells _ hwidth (fun z => hρ8.trans
        (narrowTrimmedSpatial_residue_width_lower hW hτ hξ1 hρ.le N stride hN hstridepos
          hphysical z))).choose

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem exists_allocatedCanonicalSpatial_cutoff (m : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {G : Type*} [Fintype G]
      {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
      (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
      {X : Type*} [Fintype X] {dim : ℕ} (selection : Fin dim ↪ G)
      {P p target Ecap Qstride Etau : ℝ},
      0 ≤ P → p ∈ Set.Icc 0 P → target ∈ Set.Icc 0 P →
      Ecap ∈ Set.Icc 0 P → Qstride ∈ Set.Icc 0 P → Etau ∈ Set.Icc 0 P →
      ((dim + 1 : ℕ) : ℝ) ≤ P →
      (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P →
      (Fintype.card X : ℝ) ≤ P →
      let l := allocatedSpatialLateLog (G := G) B P P + Ecap + Qstride + Etau
      normalizedTupleSideLog X (PrincipalTupleIndex B (layerSamplerDegree I n))
        selection p target l ≤ (P + C) ^ C := by
  obtain ⟨a, _, hlate⟩ := exists_allocatedSpatialLateLog_bound m
  let Xpoly : Polynomial ℕ := Polynomial.X
  let latePoly := (Xpoly + Polynomial.C a) ^ a + 3 * Xpoly
  let poly := tupleSideLogEnvelope Xpoly Xpoly latePoly
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨C, hC, ?_⟩
  intro G _ I _ n B _ X _ dim selection P p target Ecap Qstride Etau
    hP hp htarget hEcap hQstride hEtau hdim hvars hX l
  have hl₀ := allocatedSpatialLateLog_nonneg (G := G) B hP hP
  have hl : 0 ≤ l := by dsimp [l]; linarith only [hl₀, hEcap.1, hQstride.1, hEtau.1]
  have hlbound : l ≤ (P + a) ^ a + 3 * P := by
    have hb := hlate B hP hP le_rfl le_rfl hvars
    dsimp only [l]
    linarith only [hb, hEcap.2, hQstride.2, hEtau.2]
  have hG : (Fintype.card G : ℝ) ≤ P := by
    change (Fintype.card (G ⊕ PrincipalTupleIndex B (layerSamplerDegree I n)) : ℝ) ≤ P at hvars
    simp only [Fintype.card_sum, Nat.cast_add] at hvars
    linarith only [hvars, Nat.cast_nonneg (α := ℝ)
      (Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)))]
  have hindices : (Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) : ℝ) ≤ P := by
    change (Fintype.card (G ⊕ PrincipalTupleIndex B (layerSamplerDegree I n)) : ℝ) ≤ P at hvars
    simp only [Fintype.card_sum, Nat.cast_add] at hvars
    linarith only [hvars, Nat.cast_nonneg (α := ℝ) (Fintype.card G)]
  have hqdim : (Fintype.card (Unit ⊕ Fin dim) : ℝ) ≤ P := by
    simpa only [Fintype.card_sum, Fintype.card_unit, Fintype.card_fin,
      Nat.add_comm 1] using hdim
  have hs := (normalizedTuple_log_envelopes_of_le X
    (PrincipalTupleIndex B (layerSamplerDegree I n)) selection hp.1 htarget.1 hl
    hp.2 hqdim hG hindices hX).2
  apply (hs.trans (tupleSideLogEnvelope_mono hP htarget.1 hl le_rfl htarget.2 hlbound)).trans
  simpa [poly, Xpoly, latePoly, tupleSideLogEnvelope, tupleLateLogEnvelope,
    tupleWidthLogEnvelope, tupleEarlyLogEnvelope, spatialTupleToleranceLog,
    spatialDiscretizationEnvelope, spatialMeshEnvelope, spatialLipschitzCostEnvelope,
    spatialLipschitzEnvelope, spatialDisplacementEnvelope, spatialFixedProfileEnvelope,
    anisotropicSpatialCapLog, coefficientErrorVolumeLog, Polynomial.eval₂_pow] using hbound P hP

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uX uJ uO uG uI uB
open BooleanCubeKernel MeasureTheory
open scoped BigOperators Classical NNReal
attribute [local instance 2000] fullBooleanRowSetFintype

private noncomputable abbrev canonicalCoverExponent
    (m dim : ℕ) (_X : Type uX) (_G : Type uG) (I : Fin m → Type uI)
    (n : Fin m → ℕ) (_B : LayerSamplerAxis I n → Type uB) (_J : Fin m → Type uJ) : ℕ :=
  Classical.choose (exists_allocated_canonical_constructed_projection.{uX,uG,uI,uB,uJ} m dim)

variable {m : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (Cproj Vproj : Fin m → ℝ≥0)
variable {dim : ℕ}

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "sides" => allocatedPrincipalSides B U b S
local notation "fullTuple" => PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) sides

variable (X : Type uX) [Fintype X] [DecidableEq X] (modulus : ℕ) (q : X → ℕ)
local notation "refined" => residueRefinedPeriod modulus q
local notation "labels" => (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod refined)

variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S j : ℤ))
variable (label₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) →
  ZMod (residueRefinedPeriod modulus q))
variable (hcell : 0 < (principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel (residueRefinedPeriod modulus q) y = label₀)))
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (hy₀ : 0 < (containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S)
  hH hsubset (residueRefinedPeriod modulus q) label₀ hcell).weight y₀)
local notation "law" => containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S)
  hH hsubset refined label₀ hcell
local notation "wholeReference" => (fun _ : labels => y₀)

variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable [NeZero modulus] {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (hcanonical : modulus = kernelPeriodCandidate (m + 1) (goodKernelUniformCandidate selection x hx m))
variable (N : X → ℕ) {τ p target E : ℝ}
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
local notation "O" => (fun j : Fin m => (boundedBooleanJetRows (Fin dim) (Fin.val j + 1) : Type))
local notation "rows" => (fun j => (Subtype.val : O j → Finset (Fin dim)))
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
variable (hm : ∀ j ex, coefficients (poly j) ex ∈ U j)
local notation "point" d => physicalCubeRowSample U d rows poly hm
variable (signal : (X → ℤ) → ℂ) (hsignal : ∀ u, ‖signal u‖ ≤ 1)
local notation "test" => physicalCubeSiteTest (integerSelfSiteTest dim signal)

local notation "window" => spatialWindow (α := Fin dim) (trimmedSpatialRootScale τ N q) 4

variable (hN : ∀ t, 0 < N t) (hq : ∀ t, 0 < q t) (hτ : 0 < τ)
variable [CompactSpace (CoefficientTorus (K := Fin dim) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin dim) U)]
variable [BorelSpace (CoefficientTorus (K := Fin dim) U)]
variable (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
local notation "jetHaar" => Measure.pi (fun j => @Measure.pi (O j) _
  (fullBooleanRowSetFintype dim (Fin.val j + 1)) _ (fun _ : O j => ν j))

variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (SiteTorus (Finset (Fin dim)) U)]
variable [BorelSpace (SiteTorus (Finset (Fin dim)) U)]
variable (μcoeff : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μcoeff.IsAddLeftInvariant] [IsProbabilityMeasure μcoeff]

variable {Pproj Pk : ℝ}
local notation "coverExponent" => canonicalCoverExponent m dim X G I n B J
local notation "samplingExponent" => Classical.choose
  (exists_allocatedCanonicalProjection_composed_budget m dim coverExponent)
local notation "Pmass" => (Pproj + samplingExponent) ^ samplingExponent
local notation "projectionLip" => (Subtype.mk (Real.exp Pmass) (Real.exp_nonneg _) : ℝ≥0)
local notation "projectionCapNN" => (Subtype.mk (Real.exp Pmass) (Real.exp_nonneg _) : ℝ≥0)
local notation "projectionCap" => Real.exp Pmass

local notation "W" => allocatedPhysicalRootBudget B U b S (fun _ => 0)
local notation "C₀" => 1 + (S.value : ℝ) + W
local notation "Centry" => allocatedPhysicalEntryBudget B U b S (fun _ => 0)
local notation "ξ" => normalizedTupleNarrowWidth X
  (PrincipalTupleIndex B (layerSamplerDegree I n)) selection M p target
local notation "δ" => normalizedTupleRadius X selection M p target W
local notation "ρ" => normalizedTupleResolution X
  (PrincipalTupleIndex B (layerSamplerDegree I n)) selection M p target C₀ W projectionCap Centry
local notation "mesh" => min (δ / 4) (allocatedEarlyRecenteredMesh X selection M modulus p E)

include hp μ hN hq hτ hcanonical hy₀ hsignal in
theorem exists_allocatedCanonicalSlice_spatial_projected_coarse_source
    (hGproj : (Fintype.card G : ℝ) ≤ Pproj)
    (hLproj : (S.value : ℝ) ≤ Real.exp Pproj)
    (hMkPk : (M : ℝ) ≤ Real.exp Pk) (hperiodP : ((m + 1 : ℕ) : ℝ) * Pk ≤ Pproj)
    (hCactual : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ Cproj j * ‖z‖)
    (hVactual : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Vproj j)
    (hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm z‖ ≤ Cinv j * ‖z‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    {Rrank : ℝ}
    (hXmass : (Fintype.card X : ℝ) ≤ Pmass)
    (hframe : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ Pmass)
    (hstrideP : ∀ i, (q i : ℝ) ≤ Real.exp Pmass)
    (hτP : 1 / τ ≤ Real.exp Pmass)
    (hsizeMass : ∀ i, Real.exp ((Pmass + Classical.choose
      (exists_translated_physical_jet_density_window_mass.{uX,uJ,0,max uG uI uB} m dim)) ^ Classical.choose
      (exists_translated_physical_jet_density_window_mass.{uX,uJ,0,max uG uI uB} m dim)) ≤ (N i : ℝ))
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank (U j) (poly j))
    (hRrank : Real.exp ((Pmass + Classical.choose
      (exists_translated_physical_jet_density_window_mass.{uX,uJ,0,max uG uI uB} m dim)) ^ Classical.choose
      (exists_translated_physical_jet_density_window_mass.{uX,uJ,0,max uG uI uB} m dim)) ≤ Rrank)
    (hamb : (Fintype.card (CoefficientAmbientIndex (Fin dim) J) : ℝ) ≤ Pmass)
    (hjet : ((∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1)) : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp Pmass)
    {κ : ℝ}
    (hpBudget : 0 ≤ p) (hE : 0 ≤ E) (htarget : 0 ≤ target)
    (hmGeometry : ((m + 1 : ℕ) : ℝ) ≤ p)
    (hG : (Fintype.card G : ℝ) ≤ p) (hX : (Fintype.card X : ℝ) ≤ p)
    (hdim : ((dim + 1 : ℕ) : ℝ) ≤ p)
    (hMP : (M : ℝ) ≤ Real.exp p)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Real.exp p)
    (hPproj : 1 ≤ Pproj) (hmProj : (m : ℝ) ≤ Pproj)
    (hKproj : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pproj)
    (hWproj : W ≤ Real.exp Pproj)
    (hRproj : ∀ j, (R j)⁻¹ ≤ Real.exp Pproj) (hσproj : ∀ j, (σ j)⁻¹ ≤ Real.exp Pproj)
    (hcountProj : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Pproj)
    (hIproj : ∀ j, (Fintype.card (I j) : ℝ) ≤ Pproj) (hnProj : ∀ j, (n j : ℝ) ≤ Pproj)
    (hJproj : ∀ j, (Fintype.card (J j) : ℝ) ≤ Pproj)
    (hProfileProj : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Pproj)
    (hCproj : ∀ j, (Cproj j : ℝ) ≤ Real.exp Pproj) (hVproj : ∀ j, (Vproj j : ℝ) ≤ Real.exp Pproj)
    (hXproj : (Fintype.card X : ℝ) ≤ Pproj)
    (hFrameProj : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ Pproj)
    (hStrideProj : ∀ i, (q i : ℝ) ≤ Real.exp Pproj)
    (hτProj : τ⁻¹ ≤ Real.exp Pproj) (hξProj : ξ⁻¹ ≤ Real.exp Pproj)
    (hSizeProj : ∀ i, Real.exp ((Pproj + Classical.choose (Classical.choose_spec
      (exists_allocated_canonical_constructed_projection.{uX,uG,uI,uB,uJ} m dim))) ^ Classical.choose (Classical.choose_spec
      (exists_allocated_canonical_constructed_projection.{uX,uG,uI,uB,uJ} m dim))) ≤ (N i : ℝ))
    (hRankProj : Real.exp ((Pproj + Classical.choose (Classical.choose_spec
      (exists_allocated_canonical_constructed_projection.{uX,uG,uI,uB,uJ} m dim))) ^ Classical.choose (Classical.choose_spec
      (exists_allocated_canonical_constructed_projection.{uX,uG,uI,uB,uJ} m dim))) ≤ Rrank)
    {Pside : ℝ} (hProjSide : Pproj ≤ Pside) (hCapSide : Pmass ≤ Pside)
    (hpSide : p ≤ Pside) (htargetSide : target ≤ Pside)
    (hside : ∀ i, Real.exp ((Pside + Classical.choose (exists_allocatedCanonicalSpatial_cutoff.{uG,uI,uB,uX} m)) ^
      Classical.choose (exists_allocatedCanonicalSpatial_cutoff.{uG,uI,uB,uX} m)) ≤ (N i : ℝ))
    (hCells : cells.Nonempty) (bases : Finset (X → ℤ)) (hbases : bases.Nonempty) :
    let Acover := Classical.choose (exists_allocated_canonical_constructed_projection.{uX,uG,uI,uB,uJ} m dim)
    let coverLog := (Pproj + (dim + 2 : ℕ) + Acover) ^ Acover
    let cap := (allocatedAmbientFactorCap (G := G) B R σ S.value Vproj : ℝ) ^
      Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let Z := selectedJointDensityMass bases q cells V
      (allocatedJointBaseDensity B U b hb o hR hσ S X poly hm)
    let hW := allocatedPhysicalRootBudget_nonneg B U b S (fun _ => 0)
    let hξ := (canonicalSlicedSpatialChoices
      (N := PrincipalTupleIndex B (layerSamplerDegree I n)) (X := X) (m := m)
      selection hM hpBudget htarget hmGeometry hdim hG hX hMP).1
    ∀ (hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells V z),
    κ ≤ ((law).complexMean (fun y => allocatedSlicedTupleValue B U b hb o hR hσ S X poly hm
      N hN hW hτ hξ q cells hmass bases x y signal)).re →
    ∃ cover : ℕ, modulus ∣ cover ∧ 0 < cover ∧ (cover : ℝ) ≤ Real.exp coverLog ∧
    ∃ g : fullTuple → EuclideanJetLayers U O → ℝ,
      (∀ y, Continuous (g y)) ∧
      (∀ y z, g y z ∈ Set.Icc (0 : ℝ) cap) ∧
      (∀ y, Integrable (g y) jetHaar) ∧
      (∀ y, (∫ z, g y z ∂jetHaar) = 1) ∧
      (∀ y, (realDensityMeasure μcoeff (fun z => allocatedCoefficientDensity B U b hb o hR hσ S
        (quotientIntegerCover (coefficientIntegerLattice (K := LayerSamplerVariables G I n B) U) cover z))).map
          (euclideanCoefficientJetMap U (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
            (allocatedPhysicalCubeDirections B U b S x y) rows) = realDensityMeasure jetHaar (g y)) ∧
      (∀ law₁ : FiniteProbabilityWeights fullTuple,
        ∃ F : (JetAmbientIndex O J → UnitAddCircle) → ℂ,
          LipschitzWith projectionLip F ∧ (∀ z, ‖F z‖ ≤ projectionCapNN) ∧
          ∀ z, law₁.complexMean (fun y => (g y z : ℂ)) = F (coveredJetAmbientTorus U 1 z)) ∧
    ∃ base ∈ bases, Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧
      Z * (κ - Real.exp (-Pproj) - Real.exp (-target)) - Real.exp (-E) ≤
        ((law).complexMean (allocatedRecenteredProfileTerm (τ := τ) («ξ» := ξ)
          B U b S X modulus q wholeReference x hM selection hx N hW
          (allocatedEarlyRecenteredMesh X selection M modulus p E) base cells (point cover) test
          (fun y z => (g y z : ℂ)))).re := by
  intro Acover coverLog cap V Z hW hξ hmass hsource
  have hPproj0 : 0 ≤ Pproj := zero_le_one.trans hPproj
  have hPmass : 0 ≤ Pmass := by positivity
  have hPside0 : 0 ≤ Pside := hPproj0.trans hProjSide
  have hexp := Real.exp_le_exp.mpr hProjSide
  have hnumSide : AllocatedSourceNumerics B U b S Cproj Vproj Pside :=
    ⟨hPside0, hmProj.trans hProjSide, hKproj.trans hProjSide, hLproj.trans hexp,
      fun j => (hRproj j).trans hexp, fun j => (hσproj j).trans hexp,
      fun j => (hcountProj j).trans hProjSide, fun j => (hIproj j).trans hProjSide,
      fun j => (hnProj j).trans hProjSide, fun j => (hJproj j).trans hProjSide,
      hProfileProj.trans hexp, fun j => (hCproj j).trans hexp, fun j => (hVproj j).trans hexp,
      hWproj.trans hexp⟩
  have hperiod : modulus ≤ M ^ (m + 1) := by
    rw [hcanonical]
    exact kernelPeriodCandidate_le _ _
  have hearly := (allocatedEarlyRecenteredMesh_partition_budget m X selection
    hpBudget hE hG hX hM hMP hperiod).1
  have hcutoff := (Classical.choose_spec (exists_allocatedCanonicalSpatial_cutoff.{uG,uI,uB,uX} m)).2
    (X := X) B selection hPside0 ⟨hpBudget, hpSide⟩ ⟨htarget, htargetSide⟩ ⟨hPmass, hCapSide⟩
    ⟨hPproj0, hProjSide⟩ ⟨hPproj0, hProjSide⟩ (hdim.trans hpSide)
    (hKproj.trans hProjSide) (hX.trans hpSide)
  have hactualSide (i) := (Real.exp_le_exp.mpr hcutoff).trans (hside i)
  obtain ⟨hW', hC₀, hLC, hWC, hWscale, hξ', hξ1, hδpos, hδ1, hρ, hmeshpos,
      hmeshCoarse, hmeshFine, hsize, hmesh, hρ8, hρshift, hρmove, hboundary, hsite,
      hN', hwidths, hselectedMass⟩ :=
    hnumSide.canonical_spatial_choices B U b S Cproj Vproj hR hσ selection
      hpBudget htarget hPmass hPproj0 hPproj0 hM hmGeometry hdim hG hX hMP hvars hearly
      q N hq hStrideProj hτ hτProj hactualSide
  have hmass' := hselectedMass cells hCells
  exact exists_allocatedCanonicalSlice_uniform_projected_coarse_source
    (B := B)
    (U := U)
    (b := b)
    (S := S)
    (hb := hb)
    (o := o)
    (hR := hR)
    (hσ := hσ)
    (Cproj := Cproj)
    (Vproj := Vproj)
    (X := X)
    (modulus := modulus)
    (q := q)
    (H := H)
    (step := step)
    (c := c)
    (hH := hH)
    (hsubset := hsubset)
    (label₀ := label₀)
    (hcell := hcell)
    (y₀ := y₀)
    (hy₀ := hy₀)
    (x := x)
    (hM := hM)
    (selection := selection)
    (hx := hx)
    (hcanonical := hcanonical)
    (N := N)
    (hW := hW)
    («mesh» := mesh)
    (cells := cells)
    (poly := poly)
    (hp := hp)
    (hm := hm)
    (signal := signal)
    (hsignal := hsignal)
    (hN := hN')
    (hq := hq)
    (hτ := hτ)
    (hρ := hρ)
    (hbudget := le_rfl)
    (hC₀ := hC₀)
    (hLC := hLC)
    (hWC := hWC)
    (hξ := hξ')
    (hξ1 := hξ1)
    (hsize := hsize)
    (hmesh := hmesh)
    (hρ8 := hρ8)
    (hδ := hδpos.le)
    (hρshift := hρshift)
    (hρmove := hρmove)
    (hmeshpos := hmeshpos)
    (hmass := hmass')
    (μ := μ)
    (ν := ν)
    (hXmass := hXmass)
    (hframe := hframe)
    (hstrideP := hstrideP)
    (hτP := hτP)
    (hsizeMass := hsizeMass)
    (hrank := hrank)
    (hRrank := hRrank)
    (hamb := hamb)
    (hjet := hjet)
    (hboundary := hboundary)
    (hsite := hsite modulus hperiod)
    (hpBudget := hpBudget)
    (hE := hE)
    (hG := hG)
    (hX := hX)
    (hdim := hdim)
    (hMP := hMP)
    (hvars := hvars)
    (hWscale := hWscale)
    (hmeshCoarse := hmeshCoarse)
    (hPproj := hPproj)
    (hmProj := hmProj)
    (hKproj := hKproj)
    (hWproj := hWproj)
    (hRproj := hRproj)
    (hσproj := hσproj)
    (hcountProj := hcountProj)
    (hIproj := hIproj)
    (hnProj := hnProj)
    (hJproj := hJproj)
    (hProfileProj := hProfileProj)
    (hCproj := hCproj)
    (hVproj := hVproj)
    (hXproj := hXproj)
    (hFrameProj := hFrameProj)
    (hStrideProj := hStrideProj)
    (hτProj := hτProj)
    (hξProj := hξProj)
    (hSizeProj := hSizeProj)
    (hRankProj := hRankProj)
    (hCells := hCells)
    (bases := bases)
    (hbases := hbases)
    (μcoeff := μcoeff)
    (hGproj := hGproj)
    (hLproj := hLproj)
    (hMkPk := hMkPk)
    (hperiodP := hperiodP)
    (hCactual := hCactual)
    (hVactual := hVactual)
    (hσ1 := hσ1)
    (Cinv := Cinv)
    (hCinv := hCinv)
    (hchart := hchart)
    (hsmall := hsmall)
    hsource

end Erdos3.VectorPolynomial

end

end OAI
