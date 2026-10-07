import OAI.Combinatorics.Progressions.Sampling.AllocatedSiteSamplingBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (C V : Fin m → ℝ≥0)

structure AllocatedSourceNumerics (P : ℝ) : Prop where
  nonneg : 0 ≤ P
  degree : (m : ℝ) ≤ P
  variable_count : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P
  length : (S.value : ℝ) ≤ Real.exp P
  radius_inv : ∀ j, (R j)⁻¹ ≤ Real.exp P
  width_inv : ∀ j, (σ j)⁻¹ ≤ Real.exp P
  coefficients : ∀ j : Fin m,
    (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P
  real_axes : ∀ j, (Fintype.card (I j) : ℝ) ≤ P
  integer_axes : ∀ j, (n j : ℝ) ≤ P
  ambient_axes : ∀ j, (Fintype.card (J j) : ℝ) ≤ P
  profile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P
  chart : ∀ j, (C j : ℝ) ≤ Real.exp P
  covolume : ∀ j, (V j : ℝ) ≤ Real.exp P
  root : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ Real.exp P

theorem AllocatedSourceNumerics.late_bounds {P : ℝ}
    (h : AllocatedSourceNumerics B U b S C V P)
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) :
    let W := allocatedPhysicalRootBudget B U b S (fun _ => 0)
    let l := allocatedSpatialLateLog (G := G) B P P
    let C₀ := 1 + (S.value : ℝ) + W
    let cap := (allocatedAmbientFactorCap (G := G) B R σ S.value V : ℝ) ^
      Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)
    0 ≤ W ∧ 0 ≤ l ∧ P ≤ l ∧ 1 ≤ C₀ ∧ (S.value : ℝ) ≤ C₀ ∧ W ≤ C₀ ∧
      C₀ ≤ Real.exp l ∧ cap ≤ Real.exp l ∧
      allocatedPhysicalEntryBudget B U b S (fun _ => 0) ≤ Real.exp l ∧
      W ≤ Real.exp l ∧ (probabilityProfileLipschitz : ℝ) ≤ Real.exp l := by
  have hW := allocatedPhysicalRootBudget_nonneg B U b S (fun _ => 0)
  exact ⟨hW, allocatedSpatialLateInputBounds B U b S C V h.nonneg le_rfl
    h.degree h.variable_count hR hσ h.radius_inv h.width_inv h.coefficients h.real_axes
    h.integer_axes h.ambient_axes h.profile h.length h.chart h.covolume hW h.root⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uX

def AllocatedSourceNarrowNormalization (m Knorm : ℕ) : Prop :=
  ∀ {G : Type uG} [Fintype G] [DecidableEq G]
    {I : Fin m → Type uI} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]
    {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
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
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (_hσ1 : ∀ j, σ j ≤ 1)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm z‖ ≤ Cinv j * ‖z‖)
    {dim : ℕ} (_hsmall : ∀ j, R j ≤ allocatedPhysicalChartRadius (G := G) B (Fin dim) Cinv 1 j)
    {Psp Pbase E l F : ℝ} (A : ℕ)
    (_hnum : AllocatedSourceNumerics B U b S C V Pbase)
    (_hP : 0 ≤ Psp) (_hE : 0 ≤ E) (_hPbase : Psp ≤ Pbase)
    (_hm : ((m + 1 : ℕ) : ℝ) ≤ Psp) (_hdim : ((dim + 1 : ℕ) : ℝ) ≤ Psp)
    (_hG : (Fintype.card G : ℝ) ≤ Psp) (_hl : Pbase ≤ l) (_hF : 0 ≤ F)
    {X : Type uX} [Fintype X] [DecidableEq X] (_hX : (Fintype.card X : ℝ) ≤ Psp)
    (selection : Fin dim ↪ G) {M : ℕ} (_hM : 0 < M) (_hMP : (M : ℝ) ≤ Real.exp Psp)
    (q : X → ℕ) (_hq : ∀ t, 0 < q t) (_hqP : ∀ t, (q t : ℝ) ≤ Real.exp Psp),
    let W := allocatedPhysicalRootBudget B U b S (fun _ => 0)
    let ξ := normalizedTupleNarrowWidth X (PrincipalTupleIndex B (layerSamplerDegree I n))
      selection M Psp (E + 2)
    let Q := allocatedSourceSamplingBudget m dim A Pbase E l F
    ∀ {τ : ℝ}, 0 < τ → 1 / τ ≤ Real.exp Pbase →
    ∀ (N : X → ℕ), (∀ t, Real.exp ((Q + Knorm) ^ Knorm) ≤ (N t : ℝ)) →
    ∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)),
    (∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j)) →
    ∀ (hmem : ∀ j e, coefficients (poly j) e ∈ U j) {rank : ℝ},
    (∀ j, HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) rank (U j) (poly j)) →
    Real.exp ((Q + Knorm) ^ Knorm) ≤ rank →
    ∀ (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q)),
    cells.Nonempty →
    let widths := narrowTrimmedSpatialWidths (G := G)
      (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    ∃ _hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells widths z,
    ∀ (bases : Finset (X → ℤ)), bases.Nonempty →
    let Z := selectedJointDensityMass bases q cells widths
      (allocatedJointBaseDensity B U b hb o hR hσ S X poly hmem)
    |Z - 1| ≤ Real.exp (-Q) ∧ Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧ 0 < Z ∧ Z⁻¹ ≤ 2

theorem exists_allocatedSourceNarrowNormalization (m : ℕ) :
    ∃ Knorm : ℕ, 2 ≤ Knorm ∧ AllocatedSourceNarrowNormalization.{uG,uI,uB,uJ,uX} m Knorm := by
  obtain ⟨Knorm, hKnorm, hnorm⟩ := exists_allocated_narrow_normalization m
  refine ⟨Knorm, hKnorm, ?_⟩
  unfold AllocatedSourceNarrowNormalization
  intro G _ _ I _ n B _ J _ U b R σ S hb o _ _ _ _ μ _ _ ν _ _
    hR hσ hσ1 C V hC hV Cinv hCinv hchart dim hsmall
    Psp Pbase E l F A hnum hP hE hPbase hm hdim hG hl hF
    X _ _ hX selection M hM hMP q hq hqP W ξ Q τ hτ hτP
    N hsize poly hpoly hmem rank hrank hRank cells hcells widths
  have hl0 : 0 ≤ l := hnum.nonneg.trans hl
  obtain ⟨hQ1, hBaseQ, _, _, _, _, _, _, _⟩ :=
    allocatedSourceSamplingBudget_bounds m dim A hnum.nonneg hE hl0 hF
  have hQ : 0 ≤ Q := zero_le_one.trans hQ1
  have hPspQ : Psp ≤ Q := hPbase.trans hBaseQ
  have hqdim : (Fintype.card (Unit ⊕ Fin dim) : ℝ) ≤ Pbase := by
    simpa only [Fintype.card_sum, Fintype.card_unit, Fintype.card_fin, Nat.add_comm 1] using
      hdim.trans hPbase
  obtain ⟨hwidthQ, _, hdimQ⟩ := allocatedSourceSamplingBudget_spatial m A X
    (PrincipalTupleIndex B (layerSamplerDegree I n)) selection hP hE hl0 hF hPbase hqdim
    hnum.variable_count (hX.trans hPbase)
  obtain ⟨hξ, hξ1, hξlog, _⟩ := normalizedTupleSpatialChoices
    (N := PrincipalTupleIndex B (layerSamplerDegree I n)) (X := X) (m := m)
    selection hM hP (show 0 ≤ E + 2 by linarith) hm hdim hG hX hMP
  have hexp := Real.exp_le_exp.mpr hBaseQ
  have hsmallDensity := allocatedPhysicalChartRadius_density_small B (Fin dim) Cinv R
    hCinv (fun j => (hR j).le) hsmall
  obtain ⟨_, hmass, _, hglobal⟩ := hnorm B U b S hb o μ ν hR hσ hσ1 C V hC hV
    Cinv hCinv hchart hsmallDensity hQ
    (hnum.degree.trans hBaseQ) (hnum.variable_count.trans hBaseQ) (hX.trans hPspQ) hdimQ
    (fun j => (hnum.radius_inv j).trans hexp) (fun j => (hnum.width_inv j).trans hexp)
    (fun j => (hnum.coefficients j).trans hBaseQ) (fun j => (hnum.real_axes j).trans hBaseQ)
    (fun j => (hnum.integer_axes j).trans hBaseQ) (fun j => (hnum.ambient_axes j).trans hBaseQ)
    (hnum.profile.trans hexp) (hnum.length.trans hexp)
    (fun j => (hnum.chart j).trans hexp) (fun j => (hnum.covolume j).trans hexp)
    poly hpoly hmem q hq (fun t => (hqP t).trans (Real.exp_le_exp.mpr hPspQ))
    (allocatedPhysicalRootBudget_nonneg B U b S (fun _ => 0)) (hnum.root.trans hexp)
    hτ (by simpa only [one_div] using hτP.trans hexp)
    hξ hξ1 (hξlog.trans (Real.exp_le_exp.mpr hwidthQ))
    N hsize hrank hRank cells hcells
  exact ⟨hmass, hglobal⟩

end Erdos3.VectorPolynomial

end

end OAI
