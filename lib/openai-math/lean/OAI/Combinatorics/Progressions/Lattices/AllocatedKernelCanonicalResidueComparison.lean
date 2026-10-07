import OAI.Combinatorics.Progressions.Lattices.OriginalKernelResidueRetained
import OAI.Combinatorics.Progressions.Linear.AllocatedKernelSlowBudget
import OAI.Combinatorics.Progressions.Linear.CanonicalKernelSlowParameter

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X : Type*} [Fintype G] [DecidableEq G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "budget" => allocatedPhysicalRootBudget B U basis S (fun _ => 0)
local notation "slope" => (S.value : ℝ) / (1 + budget)
local notation "Spatial" => ((Σ _ : X, Unit ⊕ Empty) → ℝ)

omit [DecidableEq G] in

theorem allocatedKernelSlowExpectation_lipschitz
    (φ : Spatial → ℂ) {K : ℝ≥0} (hφ : LipschitzWith K φ) (hbound : ∀ y, ‖φ y‖ ≤ 1) :
    LipschitzWith K (canonicalKernelSlowExpectation (G := G) slope φ) := by
  apply (canonicalKernelSlowExpectation_lipschitz slope φ hφ hbound).weaken
  apply NNReal.coe_le_coe.mp
  change (K : ℝ) * ((Fintype.card G : ℝ) * |slope|) ≤ (K : ℝ)
  exact (mul_le_mul_of_nonneg_left (allocatedKernelSlowBudget_abs_le_one B U basis S)
    K.coe_nonneg).trans_eq (mul_one (K : ℝ))

theorem allocatedKernel_canonical_residue_comparison
    (s : Empty ↪ G) (q : ℕ) [NeZero q] (hsize : q ≤ S.value)
    (hsmall : scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / S.value) < 1)
    (φ : (G → ZMod q) → Spatial → ℂ) {K : ℝ≥0}
    (hφ : ∀ r, LipschitzWith K (φ r)) (hbound : ∀ r y, ‖φ r y‖ ≤ 1) :
    ‖(FiniteProbabilityWeights.pi (fun _ : G => integerScalarCubeWeights Empty S.value S.positive)).complexMean
        (fun x => ∫ y, φ (fun g => ((x g none : ℤ) : ZMod q)) y
          ∂canonicalZeroSpatialLaw s (fun g => (x g none : ℤ))
            (scalarCubeDifferenceMatrix x) budget (S.value : ℝ)) -
      𝔼 r : G → ZMod q, ∫ z, canonicalKernelSlowExpectation slope (φ r)
        (fun g => z g none) ∂scalarCubeProductMeasure G Empty‖ ≤
      (1 + 2 * (2 * scalarCubeGridBoundaryConstant Empty + K)) *
        (Fintype.card G * ((q : ℝ) / S.value)) := by
  classical
  let F := fun (r : G → ZMod q) (z : G → Option Empty → ℝ) =>
    canonicalKernelSlowExpectation slope (φ r) (fun g => z g none)
  have hproject : LipschitzWith 1 (fun z : G → Option Empty → ℝ => fun g => z g none) := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    simp only [NNReal.coe_one, one_mul]
    apply (dist_pi_le_iff dist_nonneg).mpr
    intro g
    exact (dist_le_pi_dist (z g) (w g) none).trans (dist_le_pi_dist z w g)
  have hF (r : G → ZMod q) : LipschitzWith K (F r) := by
    simpa only [mul_one, Function.comp_def, F] using
      (allocatedKernelSlowExpectation_lipschitz B U basis S (φ r) (hφ r) (hbound r)).comp hproject
  have he := originalKernel_residue_slow_quadrature S.value q S.positive (NeZero.pos q)
    hsize (by simpa only [Measure.real, scalarCubeDomain_empty_volume, ENNReal.toReal_one]
      using hsmall) F hF
      (fun r z => canonicalKernelSlowExpectation_norm_le slope (φ r) (hbound r) _)
  have hid (x : G → IntegerScalarCubeBox Empty S.value) :
      F (fun g => ((x g none : ℤ) : ZMod q)) (fun g i => (x g i : ℝ) / S.value) =
        ∫ y, φ (fun g => ((x g none : ℤ) : ZMod q)) y
          ∂canonicalZeroSpatialLaw s (fun g => (x g none : ℤ))
            (scalarCubeDifferenceMatrix x) budget (S.value : ℝ) :=
    canonicalKernelSlowExpectation_eq s (fun g => (x g none : ℤ)) (scalarCubeDifferenceMatrix x)
      budget S.value S.value (allocatedPhysicalRootBudget_nonneg B U basis S (fun _ => 0))
      (by exact_mod_cast S.positive.ne') _ (hφ _).continuous.measurable
  simp_rw [hid] at he
  simpa only [F, Measure.real, scalarCubeDomain_empty_volume, ENNReal.toReal_one, div_one] using he

theorem allocatedKernel_canonical_residue_unitBox_comparison
    (s : Empty ↪ G) (q : ℕ) [NeZero q] (hsize : q ≤ S.value)
    (hsmall : scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / S.value) < 1)
    (φ : (G → ZMod q) → Spatial → ℂ) {K : ℝ≥0}
    (hφ : ∀ r, LipschitzWith K (φ r)) (hbound : ∀ r y, ‖φ r y‖ ≤ 1) :
    ‖(FiniteProbabilityWeights.pi (fun _ : G => integerScalarCubeWeights Empty S.value S.positive)).complexMean
        (fun x => ∫ y, φ (fun g => ((x g none : ℤ) : ZMod q)) y
          ∂canonicalZeroSpatialLaw s (fun g => (x g none : ℤ))
            (scalarCubeDifferenceMatrix x) budget (S.value : ℝ)) -
      𝔼 r : G → ZMod q, ∫ t, canonicalKernelSlowExpectation slope (φ r) t
        ∂unitBoxMeasure G‖ ≤
      (1 + 2 * (2 * scalarCubeGridBoundaryConstant Empty + K)) *
        (Fintype.card G * ((q : ℝ) / S.value)) := by
  have hid (r : G → ZMod q) :
      (∫ z, canonicalKernelSlowExpectation slope (φ r) (fun g => z g none)
        ∂scalarCubeProductMeasure G Empty) =
        ∫ t, canonicalKernelSlowExpectation slope (φ r) t ∂unitBoxMeasure G := by
    rw [← scalarCubeProductMeasure_empty_map G]
    exact (integral_map (by fun_prop : Measurable (fun z : G → Option Empty → ℝ => fun g => z g none)).aemeasurable
      (allocatedKernelSlowExpectation_lipschitz B U basis S (φ r) (hφ r) (hbound r)).continuous.measurable.aestronglyMeasurable).symm
  simpa only [hid] using
    allocatedKernel_canonical_residue_comparison B U basis S s q hsize hsmall φ hφ hbound

theorem allocatedKernel_canonical_mean_riemann
    (s : Empty ↪ G)
    (hsmall : scalarCubeGridBoundaryConstant Empty * (1 / (S.value : ℝ)) < 1)
    (φ : Spatial → ℂ) {K : ℝ≥0}
    (hφ : LipschitzWith K φ) (hbound : ∀ y, ‖φ y‖ ≤ 1) :
    ‖(FiniteProbabilityWeights.pi (fun _ : G => integerScalarCubeWeights Empty S.value S.positive)).complexMean
        (fun x => ∫ y, φ y ∂canonicalZeroSpatialLaw s (fun g => (x g none : ℤ))
          (scalarCubeDifferenceMatrix x) budget (S.value : ℝ)) -
      ∫ t, canonicalKernelSlowExpectation slope φ t ∂unitBoxMeasure G‖ ≤
      (1 + 2 * (2 * scalarCubeGridBoundaryConstant Empty + K)) *
        (Fintype.card G * (1 / (S.value : ℝ))) := by
  simpa only [Nat.cast_one, Finset.expect_const, Finset.univ_nonempty, ite_true] using
    allocatedKernel_canonical_residue_unitBox_comparison B U basis S s 1 S.positive
      (by simpa only [Nat.cast_one] using hsmall) (fun _ => φ) (fun _ => hφ) (fun _ => hbound)

theorem allocatedKernel_canonical_residue_decoupling
    (s : Empty ↪ G) (q : ℕ) [NeZero q] (hsize : q ≤ S.value)
    (hsmall : scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / S.value) < 1)
    (φ : (G → ZMod q) → Spatial → ℂ) {K : ℝ≥0}
    (hφ : ∀ r, LipschitzWith K (φ r)) (hbound : ∀ r y, ‖φ r y‖ ≤ 1) :
    ‖(FiniteProbabilityWeights.pi (fun _ : G => integerScalarCubeWeights Empty S.value S.positive)).complexMean
        (fun x => ∫ y, φ (fun g => ((x g none : ℤ) : ZMod q)) y
          ∂canonicalZeroSpatialLaw s (fun g => (x g none : ℤ))
            (scalarCubeDifferenceMatrix x) budget (S.value : ℝ)) -
      𝔼 r : G → ZMod q,
        (FiniteProbabilityWeights.pi (fun _ : G => integerScalarCubeWeights Empty S.value S.positive)).complexMean
          (fun x => ∫ y, φ r y ∂canonicalZeroSpatialLaw s (fun g => (x g none : ℤ))
            (scalarCubeDifferenceMatrix x) budget (S.value : ℝ))‖ ≤
      2 * ((1 + 2 * (2 * scalarCubeGridBoundaryConstant Empty + K)) *
        (Fintype.card G * ((q : ℝ) / S.value))) := by
  classical
  let law := FiniteProbabilityWeights.pi (fun _ : G => integerScalarCubeWeights Empty S.value S.positive)
  let C : ℝ := 1 + 2 * (2 * scalarCubeGridBoundaryConstant Empty + K)
  let E : ℝ := C * (Fintype.card G * ((q : ℝ) / S.value))
  let ref := fun r : G → ZMod q =>
    ∫ t, canonicalKernelSlowExpectation slope (φ r) t ∂unitBoxMeasure G
  let original := fun r : G → ZMod q => law.complexMean
    (fun x => ∫ y, φ r y ∂canonicalZeroSpatialLaw s (fun g => (x g none : ℤ))
      (scalarCubeDifferenceMatrix x) budget (S.value : ℝ))
  have hratio : 1 / (S.value : ℝ) ≤ (q : ℝ) / S.value :=
    div_le_div_of_nonneg_right (by exact_mod_cast (show 1 ≤ q from NeZero.one_le)) (Nat.cast_nonneg _)
  have hC : 0 ≤ C := by
    have hc := (scalarCubeGridBoundaryConstant_pos Empty).le
    dsimp only [C]
    positivity
  have hsmallOne : scalarCubeGridBoundaryConstant Empty * (1 / (S.value : ℝ)) < 1 :=
    (mul_le_mul_of_nonneg_left hratio (scalarCubeGridBoundaryConstant_pos Empty).le).trans_lt hsmall
  have hsingle (r : G → ZMod q) : ‖ref r - original r‖ ≤ E := by
    rw [norm_sub_rev]
    exact (allocatedKernel_canonical_mean_riemann B U basis S s hsmallOne (φ r) (hφ r)
      (hbound r)).trans (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hratio (Nat.cast_nonneg _)) hC)
  have havg : ‖(𝔼 r : G → ZMod q, ref r) - 𝔼 r : G → ZMod q, original r‖ ≤ E := by
    rw [← Finset.expect_sub_distrib]
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    exact (Finset.expect_le_expect (fun r _ => hsingle r)).trans_eq (by simp)
  have hjoint := allocatedKernel_canonical_residue_unitBox_comparison
    B U basis S s q hsize hsmall φ hφ hbound
  exact ((norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
    (add_le_add hjoint havg)).trans_eq (by change E + E = 2 * E; ring)

end Erdos3.VectorPolynomial

end

end OAI
