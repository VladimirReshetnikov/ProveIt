import OAI.Combinatorics.Progressions.Estimates.AllocatedCenteredNarrowAmplitudeNormalization
import OAI.Combinatorics.Progressions.Estimates.CenteredFiniteNoiseEventBound
import OAI.Combinatorics.Progressions.Estimates.NormalizedDeterminantCutoff
import OAI.Combinatorics.Progressions.Geometry.SelectedJointSpatialCutoff

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

variable {B G P : Type*} [Fintype G] [Fintype P] {n : ℕ}
variable (hn : 0 < n) (e : Fin 2 × Fin n ↪ G)
variable (bases : Finset B) (hbases : bases.Nonempty)
variable (q : Fin n → ℕ) (hq : ∀ x, 0 < q x)
variable (T : Finset (ColumnResiduePattern (Option (G ⊕ P)) (Fin n) q))
variable (V : Option (G ⊕ P) × Fin n → ℝ) (hV : ∀ z, 0 < V z)
variable (hZ : 0 < ∑' z, selectedResidueSmoothWeight q T V z)
variable (hscale : ∀ z, 8 * (probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth q V z)
variable {ηprior E : ℝ} (hpriorPos : 0 < ηprior) (hE : 0 ≤ E) (hpriorExp : ηprior⁻¹ ≤ Real.exp E)
variable (hwide : ∀ i, Real.exp (smoothMatrixBlockWidthLogBudget (2 * n * n) n 2 E) ≤
  spatialMatrixIndexWidth e q V i)
variable (D : B → (Option (G ⊕ P) × Fin n → ℤ) → ℝ) (hD0 : ∀ a z, 0 ≤ D a z)
variable (hD : 0 < selectedJointDensityMass bases q T V D)
local notation "κ" => spatialMatrixBlockThreshold n ηprior
local notation "cutoff" => spatialMatrixBlockCutoff (P := P) e κ

include hn hq hscale hpriorPos hE hpriorExp hwide in

theorem spatialMatrixBlock_joint_tilted_cutoff_bound
    {ηnorm εtest : ℝ}
    (hmass : ∀ a, |selectedResidueDensityMass q T V (D a) - 1| ≤ ηnorm)
    (htest : ∀ a,
      |(∑' z, (selectedResidueSmoothPMF q T V hV hZ z).toReal *
        (cutoff (fun t => (z t : ℝ) / V t) * D a z)) -
        ∑' z, (selectedResidueSmoothPMF q T V hV hZ z).toReal *
          cutoff (fun t => (z t : ℝ) / V t)| ≤ εtest) :
    (selectedJointFiniteLaw bases hbases q T V hV hZ D hD0 hD).mean
      (fun z => if spatialMatrixBlockBad e V (κ / 2) z.2.val then (1 : ℝ) else 0) ≤
      ηprior / 2 + (ηnorm + εtest) := by
  have hκ := spatialMatrixBlockThreshold_pos hn hpriorPos
  have hprior := spatialMatrixBlock_bad_probability_of_exp_width hn e q hq T V hV hZ hscale
    hpriorPos hE hpriorExp hwide
  apply selectedJointFiniteLaw_spatial_cutoff_bound bases hbases q T V hV hZ D hD0 hD
    cutoff (spatialMatrixBlockCutoff_range e κ) (spatialMatrixBlockBad e V (κ / 2))
    (spatialMatrixBlockBad e V κ) _ hprior hmass htest
  intro z hz
  apply spatialMatrixBlockCutoff_indicator_bounds e V hκ z
  intro t
  exact (norm_le_pi_norm (fun t => (z t : ℝ) / V t) t).trans hz

include hn hq hscale hpriorPos hE hpriorExp hwide in

theorem spatialMatrixBlock_joint_tilted_cutoff_bound_complex
    {ηnorm εtest : ℝ}
    (hmass : ∀ a, |selectedResidueDensityMass q T V (D a) - 1| ≤ ηnorm)
    (htest : ∀ a,
      ‖(∑' z, ((selectedResidueSmoothPMF q T V hV hZ z).toReal : ℂ) *
        ((cutoff (fun t => (z t : ℝ) / V t) : ℂ) * (D a z : ℂ))) -
        ∑' z, ((selectedResidueSmoothPMF q T V hV hZ z).toReal : ℂ) *
          (cutoff (fun t => (z t : ℝ) / V t) : ℂ)‖ ≤ εtest) :
    (selectedJointFiniteLaw bases hbases q T V hV hZ D hD0 hD).mean
      (fun z => if spatialMatrixBlockBad e V (κ / 2) z.2.val then (1 : ℝ) else 0) ≤
      ηprior / 2 + (ηnorm + εtest) := by
  apply spatialMatrixBlock_joint_tilted_cutoff_bound hn e bases hbases q hq T V hV hZ hscale
    hpriorPos hE hpriorExp hwide D hD0 hD hmass
  intro a
  simpa only [← Complex.ofReal_mul, ← Complex.ofReal_tsum, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] using htest a

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

theorem exists_allocated_centered_spatial_matrix_exceptional (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {nX : ℕ} {G : Type*} [Fintype G]
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
    (_hX : (nX : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (LayerSamplerVariables G I n B) × (Fin nX)) : ℝ) ≤ P)
    (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (_hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) (_hLP : (S.value : ℝ) ≤ Real.exp P)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (p : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : (Fin nX) → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : (Fin nX) → ℕ) (_hs : ∀ d, 0 < stride d) (_hsP : ∀ d, (stride d : ℝ) ≤ Real.exp P)
    {W τ ξ : ℝ} (_hW : 0 ≤ W) (_hWP : W ≤ Real.exp P)
    (_hτ : 0 < τ) (_hτP : τ⁻¹ ≤ Real.exp P)
    (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hξP : ξ⁻¹ ≤ Real.exp P)
    (N : (Fin nX) → ℕ) (_hsize : ∀ d, Real.exp ((P + A) ^ A) ≤ (N d : ℝ))
    {rank : ℝ} (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (p j))
    (_hRank : Real.exp ((P + A) ^ A) ≤ rank)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride)) (_hT : T.Nonempty),
    let widths := narrowTrimmedSpatialWidths (G := G)
      (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let density := allocatedCenteredJointDensity B U basis hb o hR hσ S p hm
    ∀ (bases : Finset (Fin nX → ℤ)) (hbases : bases.Nonempty)
      (hwidths : ∀ z, 0 < widths z)
      (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T widths z)
      (htotal : ∀ center, 0 < selectedJointDensityMass bases stride T widths (density center))
      (_hnX : 0 < nX) (e : Fin 2 × Fin nX ↪ G)
      {ηprior Ewidth : ℝ}, 0 < ηprior → 0 ≤ Ewidth → ηprior⁻¹ ≤ Real.exp Ewidth →
      (∀ z, 8 * (probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth stride widths z) →
      (∀ i, Real.exp (smoothMatrixBlockWidthLogBudget (2 * nX * nX) nX 2 Ewidth) ≤
        spatialMatrixIndexWidth e stride widths i) →
      2 / spatialMatrixBlockThreshold nX ηprior * ((nX * nX.factorial : ℕ) : ℝ) ≤ Real.exp P →
      let law := fun center => selectedJointFiniteLaw bases hbases stride T widths hwidths hZ
        (density center) (allocatedCenteredJointDensity_nonneg B U basis hb o hR hσ S p hm center)
        (htotal center)
      (centeredFiniteProbabilityMeasure μ law).real
        {z | spatialMatrixBlockBad e widths (spatialMatrixBlockThreshold nX ηprior / 2) z.2.2.val} ≤
          ηprior / 2 + 6 * positiveProjectionAccuracy P := by
  obtain ⟨A, hA, hnormalization⟩ := exists_allocated_centered_narrow_amplitude_normalization m
  refine ⟨A, hA, ?_⟩
  intro nX G _ I _ n B _ J _ U basis R σ S hb o _ _ _ _ μ _ _ ν _ _
    hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall P hP hmSize hK hX hdim
    hRP hσP hcount hI hn hJ hAP hLP hCP hVP p hp hm stride hs hsP W τ ξ hW hWP hτ hτP hξ hξ1 hξP
    N hsize rank hrank hRank T hT widths density bases hbases hwidths hZ htotal hnX e
    ηprior Ewidth hpriorPos hEwidth hpriorExp hscale hwide hLipBudget law
  obtain ⟨_, _, hraw, hmass⟩ := hnormalization B U basis S hb o μ ν hR hσ hσ1 C V hC hV
    Cinv hCinv hchart hsmall hP hmSize hK (by simpa only [Fintype.card_fin] using hX)
    hdim hRP hσP hcount hI hn hJ hAP hLP hCP hVP p hp hm stride hs hsP hW hWP
    hτ hτP hξ hξ1 hξP N hsize hrank hRank T hT
  let κ := spatialMatrixBlockThreshold nX ηprior
  have hκ : 0 < κ := spatialMatrixBlockThreshold_pos hnX hpriorPos
  let amplitude := fun x : Option (LayerSamplerVariables G I n B) × Fin nX → ℝ =>
    (spatialMatrixBlockCutoff e κ x : ℂ)
  have hamp (x) : ‖amplitude x‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (spatialMatrixBlockCutoff_range e κ x).1]
    exact (spatialMatrixBlockCutoff_range e κ x).2
  have hlip := Complex.isometry_ofReal.lipschitzWith.comp (spatialMatrixBlockCutoff_lipschitz
    (P := PrincipalTupleIndex B (layerSamplerDegree I n)) e hκ)
  have hlip' : LipschitzWith (⟨2 / κ, by positivity⟩ * ((nX * nX.factorial : ℕ) : ℝ≥0))
      amplitude := by
    simpa only [one_mul, Function.comp_def] using hlip
  have hweight (z) : Measurable (fun center => (law center).weight z) :=
    allocatedCenteredJointFiniteLaw_weight_measurable B U basis hb o hR hσ S p hm
      bases hbases stride T widths hwidths hZ htotal z
  apply centeredFiniteProbabilityMeasure_noise_event_le μ law hweight
    (fun z => spatialMatrixBlockBad e widths (κ / 2) z.2.val)
  intro center
  have h := spatialMatrixBlock_joint_tilted_cutoff_bound_complex hnX e bases hbases stride hs T
    widths hwidths hZ hscale hpriorPos hEwidth hpriorExp hwide
    (density center) (allocatedCenteredJointDensity_nonneg B U basis hb o hR hσ S p hm center)
    (htotal center) (fun base => (hmass center base).1)
    (fun base => hraw center base amplitude hamp hlip'
      (by change 2 / κ * ((nX * nX.factorial : ℕ) : ℝ) ≤ Real.exp P
          exact hLipBudget))
  exact h.trans_eq (by ring)

end Erdos3.VectorPolynomial

end

end OAI
