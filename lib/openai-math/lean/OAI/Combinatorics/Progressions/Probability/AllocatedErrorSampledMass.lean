/- Modified for ProveIt: supply the proved EuclideanJetLayers Borel structure
explicitly as OpensMeasurableSpace in the error-majorant integrable-mass proof
to avoid Lean 4.32 instance-search timeout. Theorem statements are unchanged. -/
import OAI.Combinatorics.Progressions.Estimates.CoveredJetAmbientLift
import OAI.Combinatorics.Progressions.Estimates.PhysicalJetIntegralComparison
import OAI.Combinatorics.Progressions.Fourier.AllocatedErrorStandardFourier

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable (rows : ∀ j, O j → Finset α)

local notation "scale" => (∏ a, allocatedLongJetOutputScale B U b S (O := O) a)

noncomputable def allocatedMajorantRawDensity (η A : ℝ≥0)
    (z : ∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) : ℝ :=
  allocatedGridJetDensity B U b hR hσ S x u v rows (fun a => coefficientJetAxisEquiv O I n z a.val) *
    ((η : ℝ) * A / scale) * smallBoxCutoff (mixedJetAmbientPoint U b o z)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

theorem allocatedErrorAmbientKernel_mixed_point (η A : ℝ≥0)
    (z : ∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) :
    allocatedErrorAmbientKernel B U b S o hR hσ x u v rows η A (mixedJetAmbientPoint U b o z) =
      allocatedMajorantRawDensity B U b S o hR hσ x u v rows η A z / coveredJetArrayScale (O := O) U := by
  rw [allocatedErrorAmbientKernel, allocatedGridAmbientCoordinates_point,
    allocatedGridJetInterpolation_grid, ← allocatedGridLongJetScale_covolume B U b S]
  change (η : ℝ) * A * (allocatedGridJetScale B U b S (O := O) * scale * coveredJetArrayScale (O := O) U)⁻¹ *
    (smallBoxCutoff _ * (allocatedGridJetScale B U b S (O := O) * _)) = _
  unfold allocatedMajorantRawDensity
  have hg := (allocatedGridJetScale_pos B U b S (O := O)).ne'
  have hl : scale ≠ 0 := (Finset.prod_pos (fun a _ => allocatedLongJetOutputScale_pos B U b S (O := O) a)).ne'
  have hc := (coveredJetArrayScale_pos (O := O) U).ne'
  field_simp

variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (O := O) (E := Q) U o b d
  (fun j _ => standardLatticeSmallBox (J j))

theorem allocatedCoefficientErrorMajorant_chart (η A : ℝ≥0) :
    allocatedCoefficientErrorMajorant B U b S o hR hσ x u v rows η A d =
      restrictedChartDensity chart region 1
        (fun z => allocatedMajorantRawDensity B U b S o hR hσ x u v rows η A z.1 /
          coveredJetArrayScale (O := O) U) := by
  apply restrictedChartDensity_eq_of_values chart region
    (mixedCoveredJetChart_injOn U o b hb bW d _ (fun _ _ => Subset.rfl))
  · intro z hz
    change allocatedErrorTorusKernel B U b S o hR hσ x u v rows η A
      (coveredJetAmbientTorus U d (chart z)) = _
    rw [coveredJetAmbientTorus_chart, allocatedErrorTorusKernel,
      smallBoxTorusKernel_local _ (allocatedErrorAmbientKernel_support B U b S o hR hσ x u v rows η A)]
    · exact allocatedErrorAmbientKernel_mixed_point B U b S o hR hσ x u v rows η A z.1
    · intro a
      exact (hz a.1 (mem_univ _) a.2.1 (mem_univ _)).1 a.2.2
  · intro y hy
    by_contra h
    obtain ⟨z, hz, hzn⟩ := smallBoxTorusKernel_recover
      (allocatedErrorAmbientKernel B U b S o hR hσ x u v rows η A)
      (coveredJetAmbientTorus U d y) h
    exact hy (coveredJetAmbientTorus_smallBox_mem_chart U b hb o bW d y z hz
      (allocatedErrorAmbientKernel_support B U b S o hR hσ x u v rows η A z hzn))

variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

include hb bW in
theorem allocatedCoefficientErrorMajorant_lintegral (η A : ℝ≥0) :
    (∫⁻ y, ENNReal.ofReal (allocatedCoefficientErrorMajorant B U b S o hR hσ x u v rows η A d y)
      ∂Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))) =
    ∫⁻ z in region, ENNReal.ofReal (allocatedMajorantRawDensity B U b S o hR hσ x u v rows η A z.1)
      ∂mixedCoveredJetRawReference (I := I) (O := O) (E := Q) (n := n) d := by
  rw [allocatedCoefficientErrorMajorant_chart B U b S o hR hσ x u v rows hb bW d]
  exact mixedCoveredJet_normalized_lintegral U o b hb bW d ν _
    (fun j _ => (standardLatticeSmallBox_isOpen (J j)).measurableSet) (fun _ _ => Subset.rfl) _

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable (rows : ∀ j, O j → Finset α)
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit O I n grid
local notation "scale" => (∏ a, allocatedLongJetOutputScale B U b S (O := O) a)
local notation "region" => mixedCoveredJetRegion (O := O) (E := Q) U o b d
  (fun j _ => standardLatticeSmallBox (J j))
local notation "haar" => Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))

include hb bW

theorem allocatedCoefficientErrorMajorant_mass_of_box (η A : ℝ≥0) {T : ℝ}
    (hT : 0 ≤ T)
    (hbox : ∀ z ∈ region, (split z.1).2 ∈ allocatedLongJetBox B U b S O T) :
    (∫⁻ y, ENNReal.ofReal (allocatedCoefficientErrorMajorant B U b S o hR hσ x u v rows η A d y) ∂haar) ≤
      ENNReal.ofReal ((η : ℝ) * A * (2 * T + 1) ^ Fintype.card (Σ a : LayerSamplerAxis I n, O a.1)) := by
  let μf := allocatedFrozenJetReference B U b S O
  let μl := allocatedLongJetReference B U b S O
  let μd := (PMF.uniformOfFintype (∀ j, O j → Q j → ZMod d)).toMeasure
  let μraw := (Measure.pi (fun j => mixedArrayReference (I j) (Fin (n j)) (O j))).prod μd
  let box := allocatedLongJetBox B U b S O T
  let fg := allocatedGridJetDensity B U b hR hσ S x u v rows
  let e := MeasurableEquiv.prodCongr split (MeasurableEquiv.refl (∀ j, O j → Q j → ZMod d))
  let k := box.indicator (fun _ => (η : ℝ) * A / scale)
  let F := fun z : (AllocatedFrozenJetRows B U b S O × AllocatedLongJetRows B U b S O) ×
      (∀ j, O j → Q j → ZMod d) => fg z.1.1 * k z.1.2 * (1 : ℝ)
  have hscale : 0 < scale := Finset.prod_pos (fun a _ => allocatedLongJetOutputScale_pos B U b S a)
  have hfg : Integrable fg μf ∧ (∫ z, fg z ∂μf) = 1 :=
    allocatedGridJetDensity_probability_data B U b S O hR hσ x u v rows
  have hfg0 (z) : 0 ≤ fg z := (allocatedGridJetDensity_mem_Icc B U b hR hσ S x u v rows z).1
  have hki : Integrable k μl := (integrableOn_const (allocatedLongJetBox_measure_lt_top B U b S O T).ne).integrable_indicator
    (allocatedLongJetBox_measurable B U b S O T)
  have hFi : Integrable F ((μf.prod μl).prod μd) := (hfg.1.mul_prod hki).mul_prod (integrable_const 1)
  have hk0 (z) : 0 ≤ k z := Set.indicator_nonneg (fun _ _ => by positivity) z
  have hF0 (z) : 0 ≤ F z := mul_nonneg (mul_nonneg (hfg0 _) (hk0 _)) zero_le_one
  have hone : (∫ _ : (∀ j, O j → Q j → ZMod d), (1 : ℝ) ∂μd) = 1 := by simp
  have hFm : (∫ z, F z ∂(μf.prod μl).prod μd) = ((η : ℝ) * A / scale) * μl.real box := by
    dsimp only [F]
    rw [integral_prod_mul (μ := μf.prod μl) (ν := μd)
      (fun z : AllocatedFrozenJetRows B U b S O × AllocatedLongJetRows B U b S O => fg z.1 * k z.2)
      (fun _ : (∀ j, O j → Q j → ZMod d) => (1 : ℝ)),
      hone, integral_prod_mul (μ := μf) (ν := μl) fg k, hfg.2, one_mul, mul_one]
    dsimp only [k]
    rw [integral_indicator (allocatedLongJetBox_measurable B U b S O T), setIntegral_const, smul_eq_mul]
    ring
  have hbound : ((η : ℝ) * A / scale) * μl.real box ≤
      (η : ℝ) * A * (2 * T + 1) ^ Fintype.card (Σ a : LayerSamplerAxis I n, O a.1) := by
    calc
      _ ≤ ((η : ℝ) * A / scale) * ((2 * T + 1) ^ Fintype.card (Σ a : LayerSamplerAxis I n, O a.1) * scale) :=
        mul_le_mul_of_nonneg_left (allocatedLongJetBox_measure_bound B U b S O hT) (by positivity)
      _ = _ := by field_simp [hscale.ne']
  have he : MeasurePreserving e μraw ((μf.prod μl).prod μd) :=
    (coefficientJetAxisSplit_measurePreserving O I n grid).prod (MeasurePreserving.id μd)
  have hregion : MeasurableSet region :=
    (coveredJetSourceRegion_measurable U b d _ (fun j _ => (standardLatticeSmallBox_isOpen (J j)).measurableSet)).preimage
      (mixedCoveredJetCoordinates_measurable (O := O) (B := Q) (n := n) U o d)
  rw [allocatedCoefficientErrorMajorant_lintegral B U b S o hR hσ x u v rows hb bW d ν]
  calc
    _ ≤ ∫⁻ z in region, ENNReal.ofReal (F (e z)) ∂μraw := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hregion] with z hz
      apply ENNReal.ofReal_le_ofReal
      change fg ((split z.1).1) * ((η : ℝ) * A / scale) * smallBoxCutoff (mixedJetAmbientPoint U b o z.1) ≤
        fg ((split z.1).1) * k ((split z.1).2) * 1
      dsimp only [k]
      rw [Set.indicator_of_mem (hbox z hz), mul_one]
      exact mul_le_of_le_one_right (mul_nonneg (hfg0 _) (by positivity)) (smallBoxCutoff_range _).2
    _ ≤ ∫⁻ z, ENNReal.ofReal (F (e z)) ∂μraw := lintegral_mono' Measure.restrict_le_self le_rfl
    _ = ∫⁻ z, ENNReal.ofReal (F z) ∂(μf.prod μl).prod μd :=
      he.lintegral_comp_emb e.measurableEmbedding (fun z => ENNReal.ofReal (F z))
    _ = ENNReal.ofReal (((η : ℝ) * A / scale) * μl.real box) := by
      rw [← ofReal_integral_eq_lintegral_ofReal hFi (Filter.Eventually.of_forall hF0), hFm]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hbound

theorem allocatedCoefficientErrorMajorant_mass (η A : ℝ≥0) (C : Fin m → ℝ)
    (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖) :
    (∫⁻ y, ENNReal.ofReal (allocatedCoefficientErrorMajorant B U b S o hR hσ x u v rows η A d y) ∂haar) ≤
      ENNReal.ofReal ((η : ℝ) * A *
        (2 * (∑ j, C j * ((Fintype.card (J j) : ℝ) + 1)) + 1) ^
          Fintype.card (Σ a : LayerSamplerAxis I n, O a.1)) := by
  let T := ∑ j, C j * ((Fintype.card (J j) : ℝ) + 1)
  have hT : 0 ≤ T := Finset.sum_nonneg (fun j _ => mul_nonneg (hC j) (by positivity))
  have hCT (j) : C j * ((Fintype.card (J j) : ℝ) + 1) ≤ T :=
    Finset.single_le_sum (f := fun i => C i * ((Fintype.card (J i) : ℝ) + 1))
      (fun i _ => mul_nonneg (hC i) (by positivity)) (Finset.mem_univ j)
  apply allocatedCoefficientErrorMajorant_mass_of_box B U b S o hR hσ x u v rows hb bW d ν η A hT
  intro z hz
  apply allocatedAmbient_long_rows_box B U b S O o hC hT hchart hCT z.1
  intro a
  exact ((hz a.1 (mem_univ _) a.2.1 (mem_univ _)).1 a.2.2).le.trans (by norm_num)

theorem allocatedCoefficientErrorMajorant_integrable_mass (η A : ℝ≥0) (C V : Fin m → ℝ≥0)
    (hC : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖)
    (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j) :
    Integrable (allocatedCoefficientErrorMajorant B U b S o hR hσ x u v rows η A d) haar ∧
    (∫ y, allocatedCoefficientErrorMajorant B U b S o hR hσ x u v rows η A d y ∂haar) ≤
      (η : ℝ) * A * (2 * (∑ j, (C j : ℝ) * ((Fintype.card (J j) : ℝ) + 1)) + 1) ^
        Fintype.card (Σ a : LayerSamplerAxis I n, O a.1) := by
  let : OpensMeasurableSpace (EuclideanJetLayers U O) :=
    @BorelSpace.opensMeasurable _ _ _ (euclideanJetLayers_borel U)
  let g := allocatedCoefficientErrorMajorant B U b S o hR hσ x u v rows η A d
  have hp := allocatedErrorTorusKernel_bounds B U b S o hR hσ x u v rows η A C V hC hV
  have hg0 (y) : 0 ≤ g y := (hp.1 (coveredJetAmbientTorus U d y)).1
  have hgc : Continuous g :=
    allocatedCoefficientErrorMajorant_continuous B U b S o hR hσ x u v rows η A d C V hC hV
  have hgi : Integrable g haar := by
    apply (integrable_const (allocatedErrorKernelCap B U b S (O := O) η A V : ℝ)).mono'
      hgc.measurable.aestronglyMeasurable
    filter_upwards [] with y
    rw [Real.norm_eq_abs, abs_of_nonneg (hg0 y)]
    exact (hp.1 (coveredJetAmbientTorus U d y)).2
  refine ⟨hgi, ?_⟩
  have hmass := allocatedCoefficientErrorMajorant_mass B U b S o hR hσ x u v rows hb bW d ν η A
    (fun j => (C j : ℝ)) (fun j => (C j).coe_nonneg) hC
  change (∫⁻ y, ENNReal.ofReal (g y) ∂haar) ≤ _ at hmass
  rw [← ofReal_integral_eq_lintegral_ofReal hgi (Filter.Eventually.of_forall hg0)] at hmass
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hmass

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory Module Submodule VectorPolynomial
open scoped BigOperators Classical NNReal

theorem exists_allocated_error_sampled_mass (m q : ℕ) :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ {X : Type*} [Fintype X] [DecidableEq X]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (Fin q) × X) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := Fin q) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin q) U)] [BorelSpace (CoefficientTorus (K := Fin q) U)]
    (μ : Measure (CoefficientTorus (K := Fin q) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j)
    (d : ℕ) [NeZero d]
    (stride : X → ℕ) (_hs : ∀ x, 0 < stride x)
    {R S₀ ρ ε : ℝ} (_hS : 0 ≤ S₀) (_hSP : S₀ ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ x, (stride x : ℝ) ≤ S₀)
    (H : X → ℝ) (_hsize : ∀ x, Real.exp ((P + K) ^ K) ≤ H x)
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) H R (U j) (p j))
    (_hR : Real.exp ((P + K) ^ K) ≤ R)
    (cells : Finset (ColumnResiduePattern (Option (Fin q)) X stride)) (_hcells : cells.Nonempty)
    (W : Option (Fin q) × X → ℝ) (_hW : ∀ z, 0 < W z) (_hwidth : ∀ z, ρ * H z.2 ≤ W z)
    {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R₀ σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R₀ σ)
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR₀ : ∀ j, 0 < R₀ j) (hσ : ∀ j, 0 < σ j)
    {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
    (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
      (allocatedPrincipalSides B U b S))
    (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
      (allocatedPrincipalSides B U b S))
    (rows : ∀ j : Fin m, BoundedBooleanJet (Fin q) (j.val + 1) → Finset α)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (period : ℕ) [NeZero period]
    (_hperiod : ∀ j, integerScalarLattice (BoundedBooleanJet (Fin q) (j.val + 1)) (period : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (η : ℝ≥0) (C V : Fin m → ℝ≥0)
    (_hC : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    {δ L : ℝ} (_hδ : 0 < δ) (_hL : 0 ≤ L)
    (_hamb : (Fintype.card (JetAmbientIndex (fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)) J) : ℝ) ≤ L)
    (_hδL : δ⁻¹ ≤ Real.exp L),
    let O := fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)
    let A := Real.toNNReal (coefficientDeckPeriodCap O Q period)
    (allocatedErrorKernelLip B U b S (O := O) η A C V : ℝ) ≤ Real.exp L →
    Real.exp ((2 * L + 2) ^ 4) ≤ Real.exp P →
    Real.exp (2 * L * (2 * L + 2) ^ 4) * allocatedErrorKernelCap B U b S (O := O) η A V ≤ Real.exp P →
    let g := allocatedCoefficientErrorMajorant B U b S o hR₀ hσ x u v rows η A d
    let error := restrictedChartDensity (mixedCoveredJetChart U o b hb bW d)
      (mixedCoveredJetRegion (O := O) (E := Q) U o b d (fun j _ => standardLatticeClosedQuarterBox (J j)))
      1 (fun z : MixedCoveredJetSource I O Q n d =>
        allocatedCoveredFixedFactor B U b hR₀ hσ S x u v rows Q d z.1 z.2 *
          ((η : ℝ) / (∏ a, allocatedLongJetOutputScale B U b S (O := O) a)))
    let M := (η : ℝ) * A *
      (2 * (∑ j, (C j : ℝ) * ((Fintype.card (J j) : ℝ) + 1)) + 1) ^
        Fintype.card (Σ a : LayerSamplerAxis I n, O a.1)
    ∃ _hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells W z,
      selectedResidueDensityMass stride cells W
        (fun z => g (physicalCubeEuclideanSample U d p hm (standardPhysicalCubeOutput z))) ≤ M + 2 * δ + ε ∧
      selectedResidueDensityMass stride cells W
        (fun z => error (physicalCubeEuclideanSample U d p hm (standardPhysicalCubeOutput z))) ≤ M + 2 * δ + ε := by
  obtain ⟨K, hK, htest⟩ := exists_physical_jet_integral_comparison m q
  refine ⟨K, hK, ?_⟩
  intro X _ _ J _ P hP hn hdim U _ _ _ μ _ _ ν _ _ p hp hm d _ stride hs R S₀ ρ ε
    hS hSP hρ hε hρP hεP hstride H hsize hrank hR cells hcells W hW hwidth
    G _ I _ n B _ b R₀ σ S o hR₀ hσ α _ x u v rows _ hb Q _ bW period _ hperiod
    η C V hC hV δ L hδ hL hamb hδL O A hLip hfreqP hcoeffP g error M
  obtain ⟨F, inst, frequency, c, _hcard, hfreq, hsum, happrox⟩ :=
    exists_allocated_error_standard_fourier B U b S o hR₀ hσ x u v rows 1 η A C V
      hC hV hδ hL hamb hLip hδL
  let _ := inst
  simp only [Nat.cast_one, mul_one] at hfreq
  let g₁ := allocatedCoefficientErrorMajorant B U b S o hR₀ hσ x u v rows η A 1
  have hmass := allocatedCoefficientErrorMajorant_integrable_mass B U b S o hR₀ hσ x u v rows
    hb bW 1 ν η A C V hC hV
  obtain ⟨hZ, hclose⟩ := htest hP hn hdim U μ ν (by positivity) hfreqP frequency hfreq c
    (by positivity) hcoeffP hsum p hp hm 1 Nat.zero_lt_one (by simpa only [Nat.cast_one] using Real.one_le_exp hP) stride hs
    hS hSP hρ hε hρP hεP hstride H hsize hrank hR cells hcells W hW hwidth g₁ hmass.1 hδ.le happrox
  have hbound : selectedResidueDensityMass stride cells W
      (fun z => g (physicalCubeEuclideanSample U d p hm (standardPhysicalCubeOutput z))) ≤ M + 2 * δ + ε := by
    have he := (abs_le.mp hclose).2
    have hm' : (∫ y, g₁ y ∂(Measure.pi (fun j => Measure.pi (fun _ : O j => ν j)))) ≤ M := hmass.2
    dsimp only [g]
    simp_rw [allocatedCoefficientErrorMajorant_sample B U b S o hR₀ hσ x u v rows η A d p hm]
    change selectedResidueDensityMass stride cells W
      (fun z => g₁ (physicalCubeEuclideanSample U 1 p hm (standardPhysicalCubeOutput z))) ≤ _
    linarith
  refine ⟨hZ, hbound, ?_⟩
  apply (selectedResidueDensityMass_mono stride cells W hW hZ (fun z => ?_)).trans hbound
  exact allocatedCoefficientError_le_majorant B U b S o hR₀ hσ x u v rows hb bW d period
    hperiod η C V hC hV _

end Erdos3.BooleanCubeKernel

end

end OAI
