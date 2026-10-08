/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Supply the proved EuclideanJetLayers Borel structure explicitly as
OpensMeasurableSpace in the integrable-mass proof to avoid instance-search
timeout. All upstream theorem statements are unchanged. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Estimates.CoveredJetAmbientLift
import OAI.Combinatorics.Progressions.Estimates.PhysicalJetCoverCancellation

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (p : ∀ a : {a // allocatedGridAxis (I := I) U b S.value a}, PMF (CoefficientJetAxisRow O a.val))

noncomputable def allocatedProbabilityAmbientKernel (η A : ℝ≥0) (z : JetAmbientIndex O J → ℝ) : ℝ :=
  (η : ℝ) * A *
    (∏ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ^ Fintype.card (O j)) *
    (smallBoxCutoff z * allocatedProbabilityGridInterpolation B U b S p
      (allocatedGridAmbientCoordinates B U b S o z))

theorem allocatedProbabilityAmbientKernel_support (η A : ℝ≥0) (z : JetAmbientIndex O J → ℝ)
    (hz : allocatedProbabilityAmbientKernel B U b S o p η A z ≠ 0) :
    ∀ i, |z i| < 1 / 2 := by
  apply smallBoxCutoff_support z
  intro he
  exact hz (by simp only [allocatedProbabilityAmbientKernel, he, zero_mul, mul_zero])

theorem allocatedProbabilityAmbientKernel_quarter (η A : ℝ≥0)
    (z : ∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ))
    (hz : ∀ i, |mixedJetAmbientPoint U b o z i| ≤ 1 / 4) :
    allocatedProbabilityAmbientKernel B U b S o p η A (mixedJetAmbientPoint U b o z) =
      (η : ℝ) * A *
      (∏ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ^ Fintype.card (O j)) *
      allocatedProbabilityGridInterpolation B U b S p
        (allocatedGridNormalizedRows B U b S (fun a => coefficientJetAxisEquiv O I n z a.val)) := by
  rw [allocatedProbabilityAmbientKernel, smallBoxCutoff_one _ hz, one_mul,
    allocatedGridAmbientCoordinates_point]

theorem allocatedProbabilityAmbientKernel_bounds (η A : ℝ≥0) (C V : Fin m → ℝ≥0)
    (hC : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖)
    (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j) :
    let K : ℝ≥0 := (S.value : ℝ≥0) ^ (layerTailDegree m + 1)
    let D := Fintype.card (Σ a : LayerSamplerAxis I n, O a.1)
    let N := Fintype.card {a // allocatedGridAxis (I := I) U b S.value a}
    let M : ℝ≥0 := (K ^ D) ^ N
    let L : ℝ≥0 := N * (D * (2 * K ^ 2) * K ^ D) * M
    let W : ℝ≥0 := η * A * ∏ j, V j ^ Fintype.card (O j)
    (∀ z, 0 ≤ allocatedProbabilityAmbientKernel B U b S o p η A z ∧
      allocatedProbabilityAmbientKernel B U b S o p η A z ≤ W * M) ∧
    LipschitzWith (W * (L * (∑ j, C j * Fintype.card (J j)) + M * 8))
      (allocatedProbabilityAmbientKernel B U b S o p η A) := by
  intro K D N M L W
  let F := allocatedProbabilityGridInterpolation B U b S p
  let c : ℝ := (η : ℝ) * A *
    ∏ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ^ Fintype.card (O j)
  have hc0 : 0 ≤ c := mul_nonneg (mul_nonneg η.coe_nonneg A.coe_nonneg)
    (Finset.prod_nonneg (fun j _ => pow_nonneg (hV j).1 _))
  have hc : c ≤ W := by
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg η.coe_nonneg A.coe_nonneg)
    exact_mod_cast Finset.prod_le_prod₀ (fun j _ => pow_nonneg (hV j).1 _)
      (fun j _ => pow_le_pow_left₀ (hV j).1 (hV j).2 _)
  have hf := allocatedProbabilityGridInterpolation_uniform_bounds B U b S p
  have hf0 (z) : 0 ≤ F z := (hf.1 z).1
  have hfcap (z) : |F z| ≤ (M : ℝ) := by
    rw [abs_of_nonneg (hf0 z)]
    simpa only [M, K, D, N, NNReal.coe_pow] using (hf.1 z).2
  have hfl : LipschitzWith (L * (∑ j, C j * Fintype.card (J j)))
      (fun z => F (allocatedGridAmbientCoordinates B U b S o z)) :=
    hf.2.comp (allocatedGridAmbientCoordinates_lipschitz B U b S o C hC)
  have hcut := smallBoxCutoff_mul_lipschitz _ hfl
    (fun z => hfcap (allocatedGridAmbientCoordinates B U b S o z))
  have hcut0 (z : JetAmbientIndex O J → ℝ) :
      0 ≤ smallBoxCutoff z * F (allocatedGridAmbientCoordinates B U b S o z) :=
    mul_nonneg (smallBoxCutoff_range z).1 (hf0 _)
  have hcutcap (z : JetAmbientIndex O J → ℝ) :
      |smallBoxCutoff z * F (allocatedGridAmbientCoordinates B U b S o z)| ≤ (M : ℝ) := by
    rw [abs_of_nonneg (hcut0 z)]
    exact (mul_le_mul_of_nonneg_right (smallBoxCutoff_range z).2 (hf0 _)).trans
      (by simpa only [one_mul, abs_of_nonneg (hf0 _)] using hfcap (allocatedGridAmbientCoordinates B U b S o z))
  refine ⟨fun z => ⟨mul_nonneg hc0 (hcut0 z), ?_⟩, ?_⟩
  · change c * (smallBoxCutoff z * F (allocatedGridAmbientCoordinates B U b S o z)) ≤
      (W : ℝ) * (M : ℝ)
    exact mul_le_mul hc ((le_abs_self _).trans (hcutcap z)) (hcut0 z) W.coe_nonneg
  · have h := lipschitz_real_mul_of_bounds (Bf := W) (Bg := M) (fun _ => c)
      (fun z => smallBoxCutoff z * F (allocatedGridAmbientCoordinates B U b S o z))
      (LipschitzWith.const c) hcut (fun _ => by rwa [abs_of_nonneg hc0]) hcutcap
    apply LipschitzWith.of_dist_le_mul
    intro z w
    change dist (c * (smallBoxCutoff z * F (allocatedGridAmbientCoordinates B U b S o z)))
      (c * (smallBoxCutoff w * F (allocatedGridAmbientCoordinates B U b S o w))) ≤ _
    have hh := h.dist_le_mul z w
    simpa only [mul_zero, add_zero] using hh

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (p : ∀ a : {a // allocatedGridAxis (I := I) U b S.value a}, PMF (CoefficientJetAxisRow O a.val))

noncomputable def allocatedProbabilityTorusKernel (η A : ℝ≥0) : (JetAmbientIndex O J → UnitAddCircle) → ℝ :=
  smallBoxTorusKernel (allocatedProbabilityAmbientKernel B U b S o p η A)

noncomputable def allocatedProbabilityMajorant (η A : ℝ≥0) (d : ℕ)
    (y : EuclideanJetLayers U O) : ℝ :=
  allocatedProbabilityTorusKernel B U b S o p η A (coveredJetAmbientTorus U d y)

theorem allocatedProbabilityTorusKernel_bounds (η A : ℝ≥0) (C V : Fin m → ℝ≥0)
    (hC : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖)
    (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j) :
    (∀ z, 0 ≤ allocatedProbabilityTorusKernel B U b S o p η A z ∧
      allocatedProbabilityTorusKernel B U b S o p η A z ≤
        allocatedErrorKernelCap B U b S (O := O) η A V) ∧
    LipschitzWith (allocatedErrorKernelLip B U b S (O := O) η A C V)
      (allocatedProbabilityTorusKernel B U b S o p η A) := by
  have h := allocatedProbabilityAmbientKernel_bounds B U b S o p η A C V hC hV
  exact ⟨smallBoxTorusKernel_range _ (NNReal.coe_nonneg _) h.1
      (allocatedProbabilityAmbientKernel_support B U b S o p η A),
    smallBoxTorusKernel_lipschitz _ h.2 (fun z => (h.1 z).1)
      (allocatedProbabilityAmbientKernel_support B U b S o p η A)⟩

theorem allocatedProbabilityMajorant_continuous (η A : ℝ≥0) (d : ℕ) (C V : Fin m → ℝ≥0)
    (hC : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖)
    (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j) :
    Continuous (allocatedProbabilityMajorant B U b S o p η A d) :=
  (allocatedProbabilityTorusKernel_bounds B U b S o p η A C V hC hV).2.continuous.comp
    (coveredJetAmbientTorus_continuous U d)

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
variable (p : ∀ a : {a // allocatedGridAxis (I := I) U b S.value a}, PMF (CoefficientJetAxisRow O a.val))

local notation "scale" => (∏ a, allocatedLongJetOutputScale B U b S (O := O) a)

noncomputable def allocatedProbabilityRawDensity (η A : ℝ≥0)
    (z : ∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) : ℝ :=
  allocatedProbabilityGridDensity B U b S p (fun a => coefficientJetAxisEquiv O I n z a.val) *
    ((η : ℝ) * A / scale) * smallBoxCutoff (mixedJetAmbientPoint U b o z)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

theorem allocatedProbabilityAmbientKernel_mixed_point (η A : ℝ≥0)
    (z : ∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) :
    allocatedProbabilityAmbientKernel B U b S o p η A (mixedJetAmbientPoint U b o z) =
      allocatedProbabilityRawDensity B U b S o p η A z / coveredJetArrayScale (O := O) U := by
  rw [allocatedProbabilityAmbientKernel, allocatedGridAmbientCoordinates_point,
    allocatedProbabilityGridInterpolation_grid, ← allocatedGridLongJetScale_covolume B U b S]
  change (η : ℝ) * A * (allocatedGridJetScale B U b S (O := O) * scale * coveredJetArrayScale (O := O) U)⁻¹ *
    (smallBoxCutoff _ * (allocatedGridJetScale B U b S (O := O) * _)) = _
  unfold allocatedProbabilityRawDensity
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

theorem allocatedProbabilityMajorant_chart (η A : ℝ≥0) :
    allocatedProbabilityMajorant B U b S o p η A d =
      restrictedChartDensity chart region 1
        (fun z => allocatedProbabilityRawDensity B U b S o p η A z.1 /
          coveredJetArrayScale (O := O) U) := by
  apply restrictedChartDensity_eq_of_values chart region
    (mixedCoveredJetChart_injOn U o b hb bW d _ (fun _ _ => Subset.rfl))
  · intro z hz
    change allocatedProbabilityTorusKernel B U b S o p η A
      (coveredJetAmbientTorus U d (chart z)) = _
    rw [coveredJetAmbientTorus_chart, allocatedProbabilityTorusKernel,
      smallBoxTorusKernel_local _ (allocatedProbabilityAmbientKernel_support B U b S o p η A)]
    · exact allocatedProbabilityAmbientKernel_mixed_point B U b S o p η A z.1
    · intro a
      exact (hz a.1 (mem_univ _) a.2.1 (mem_univ _)).1 a.2.2
  · intro y hy
    by_contra h
    obtain ⟨z, hz, hzn⟩ := smallBoxTorusKernel_recover
      (allocatedProbabilityAmbientKernel B U b S o p η A)
      (coveredJetAmbientTorus U d y) h
    exact hy (coveredJetAmbientTorus_smallBox_mem_chart U b hb o bW d y z hz
      (allocatedProbabilityAmbientKernel_support B U b S o p η A z hzn))

theorem allocatedProbabilityQuarter_le_majorant
    (η A : ℝ≥0) (C V : Fin m → ℝ≥0)
    (hC : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖)
    (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (y : EuclideanJetLayers U O) :
    restrictedChartDensity (mixedCoveredJetChart U o b hb bW d)
      (mixedCoveredJetRegion (O := O) (E := Q) U o b d
        (fun j _ => standardLatticeClosedQuarterBox (J j))) 1
      (fun z : MixedCoveredJetSource I O Q n d =>
        allocatedProbabilityGridDensity B U b S p
          (fun a => coefficientJetAxisEquiv O I n z.1 a.val) *
          (((η : ℝ) * A) / scale) / coveredJetArrayScale (O := O) U) y ≤
      allocatedProbabilityMajorant B U b S o p η A d y := by
  let small := mixedCoveredJetRegion (O := O) (E := Q) U o b d
    (fun j _ => standardLatticeClosedQuarterBox (J j))
  by_cases hy : y ∈ (mixedCoveredJetChart U o b hb bW d) '' small
  · obtain ⟨z, hz, rfl⟩ := hy
    have hquarter : ∀ a, |mixedJetAmbientPoint U b o z.1 a| ≤ 1 / 4 := by
      intro a
      exact (hz a.1 (Set.mem_univ _) a.2.1 (Set.mem_univ _)).1 a.2.2
    rw [restrictedChartDensity_apply (mixedCoveredJetChart U o b hb bW d) small 1 _
      (mixedCoveredJetChart_injOn U o b hb bW d _
        (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))) hz, one_mul]
    change _ ≤ allocatedProbabilityTorusKernel B U b S o p η A
      (coveredJetAmbientTorus U d (mixedCoveredJetChart U o b hb bW d z))
    rw [coveredJetAmbientTorus_chart, allocatedProbabilityTorusKernel,
      smallBoxTorusKernel_local _ (allocatedProbabilityAmbientKernel_support B U b S o p η A)
        _ (fun a => lt_of_le_of_lt (hquarter a) (by norm_num)),
      allocatedProbabilityAmbientKernel_mixed_point]
    simp only [allocatedProbabilityRawDensity, smallBoxCutoff_one _ hquarter, mul_one, le_refl]
  · rw [restrictedChartDensity_zero (mixedCoveredJetChart U o b hb bW d) small 1 _ hy]
    exact ((allocatedProbabilityTorusKernel_bounds B U b S o p η A C V hC hV).1 _).1

variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

include hb bW in
theorem allocatedProbabilityMajorant_lintegral (η A : ℝ≥0) :
    (∫⁻ y, ENNReal.ofReal (allocatedProbabilityMajorant B U b S o p η A d y)
      ∂Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))) =
    ∫⁻ z in region, ENNReal.ofReal (allocatedProbabilityRawDensity B U b S o p η A z.1)
      ∂mixedCoveredJetRawReference (I := I) (O := O) (E := Q) (n := n) d := by
  rw [allocatedProbabilityMajorant_chart B U b S o p hb bW d]
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
variable (p : ∀ a : {a // allocatedGridAxis (I := I) U b S.value a}, PMF (CoefficientJetAxisRow O a.val))

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

theorem allocatedProbabilityMajorant_mass_of_box (η A : ℝ≥0) {T : ℝ}
    (hT : 0 ≤ T)
    (hbox : ∀ z ∈ region, (split z.1).2 ∈ allocatedLongJetBox B U b S O T) :
    (∫⁻ y, ENNReal.ofReal (allocatedProbabilityMajorant B U b S o p η A d y) ∂haar) ≤
      ENNReal.ofReal ((η : ℝ) * A * (2 * T + 1) ^ Fintype.card (Σ a : LayerSamplerAxis I n, O a.1)) := by
  let μf := allocatedFrozenJetReference B U b S O
  let μl := allocatedLongJetReference B U b S O
  let μd := (PMF.uniformOfFintype (∀ j, O j → Q j → ZMod d)).toMeasure
  let μraw := (Measure.pi (fun j => mixedArrayReference (I j) (Fin (n j)) (O j))).prod μd
  let box := allocatedLongJetBox B U b S O T
  let fg := allocatedProbabilityGridDensity B U b S p
  let e := MeasurableEquiv.prodCongr split (MeasurableEquiv.refl (∀ j, O j → Q j → ZMod d))
  let k := box.indicator (fun _ => (η : ℝ) * A / scale)
  let F := fun z : (AllocatedFrozenJetRows B U b S O × AllocatedLongJetRows B U b S O) ×
      (∀ j, O j → Q j → ZMod d) => fg z.1.1 * k z.1.2 * (1 : ℝ)
  have hscale : 0 < scale := Finset.prod_pos (fun a _ => allocatedLongJetOutputScale_pos B U b S a)
  have hfg : Integrable fg μf ∧ (∫ z, fg z ∂μf) = 1 :=
    allocatedProbabilityGridDensity_mass B U b S p
  have hfg0 (z) : 0 ≤ fg z := allocatedProbabilityGridDensity_nonneg B U b S p z
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
  rw [allocatedProbabilityMajorant_lintegral B U b S o p hb bW d ν]
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

theorem allocatedProbabilityMajorant_mass (η A : ℝ≥0) (C : Fin m → ℝ)
    (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖) :
    (∫⁻ y, ENNReal.ofReal (allocatedProbabilityMajorant B U b S o p η A d y) ∂haar) ≤
      ENNReal.ofReal ((η : ℝ) * A *
        (2 * (∑ j, C j * ((Fintype.card (J j) : ℝ) + 1)) + 1) ^
          Fintype.card (Σ a : LayerSamplerAxis I n, O a.1)) := by
  let T := ∑ j, C j * ((Fintype.card (J j) : ℝ) + 1)
  have hT : 0 ≤ T := Finset.sum_nonneg (fun j _ => mul_nonneg (hC j) (by positivity))
  have hCT (j) : C j * ((Fintype.card (J j) : ℝ) + 1) ≤ T :=
    Finset.single_le_sum (f := fun i => C i * ((Fintype.card (J i) : ℝ) + 1))
      (fun i _ => mul_nonneg (hC i) (by positivity)) (Finset.mem_univ j)
  apply allocatedProbabilityMajorant_mass_of_box B U b S o p hb bW d ν η A hT
  intro z hz
  apply allocatedAmbient_long_rows_box B U b S O o hC hT hchart hCT z.1
  intro a
  exact ((hz a.1 (mem_univ _) a.2.1 (mem_univ _)).1 a.2.2).le.trans (by norm_num)

theorem allocatedProbabilityMajorant_integrable_mass (η A : ℝ≥0) (C V : Fin m → ℝ≥0)
    (hC : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖)
    (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j) :
    Integrable (allocatedProbabilityMajorant B U b S o p η A d) haar ∧
    (∫ y, allocatedProbabilityMajorant B U b S o p η A d y ∂haar) ≤
      (η : ℝ) * A * (2 * (∑ j, (C j : ℝ) * ((Fintype.card (J j) : ℝ) + 1)) + 1) ^
        Fintype.card (Σ a : LayerSamplerAxis I n, O a.1) := by
  let : OpensMeasurableSpace (EuclideanJetLayers U O) :=
    @BorelSpace.opensMeasurable _ _ _ (euclideanJetLayers_borel U)
  let g := allocatedProbabilityMajorant B U b S o p η A d
  have hp := allocatedProbabilityTorusKernel_bounds B U b S o p η A C V hC hV
  have hg0 (y) : 0 ≤ g y := (hp.1 (coveredJetAmbientTorus U d y)).1
  have hgc : Continuous g :=
    allocatedProbabilityMajorant_continuous B U b S o p η A d C V hC hV
  have hgi : Integrable g haar := by
    apply (integrable_const (allocatedErrorKernelCap B U b S (O := O) η A V : ℝ)).mono'
      hgc.measurable.aestronglyMeasurable
    filter_upwards [] with y
    rw [Real.norm_eq_abs, abs_of_nonneg (hg0 y)]
    exact (hp.1 (coveredJetAmbientTorus U d y)).2
  refine ⟨hgi, ?_⟩
  have hmass := allocatedProbabilityMajorant_mass B U b S o p hb bW d ν η A
    (fun j => (C j : ℝ)) (fun j => (C j).coe_nonneg) hC
  change (∫⁻ y, ENNReal.ofReal (g y) ∂haar) ≤ _ at hmass
  rw [← ofReal_integral_eq_lintegral_ofReal hgi (Filter.Eventually.of_forall hg0)] at hmass
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hmass

end Erdos3.VectorPolynomial

end

end OAI
