import OAI.Combinatorics.Progressions.Estimates.ShiftedProductTestError

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {K X : Type*} [Fintype K] [Fintype X]

noncomputable def selectedResidueCellWeight (modulus : X → ℕ)
    (T : Finset (ColumnResiduePattern K X modulus)) (V : K × X → ℝ) (r : T) : ℝ :=
  (∑' z, residueSmoothWeight (columnResidueRepresentative modulus r.val) modulus V z) /
    (∑' z, selectedResidueSmoothWeight modulus T V z)

theorem selectedResidueCellWeight_nonneg (modulus : X → ℕ)
    (T : Finset (ColumnResiduePattern K X modulus)) (V : K × X → ℝ) (r : T) :
    0 ≤ selectedResidueCellWeight modulus T V r := by
  apply div_nonneg
  · apply tsum_nonneg
    intro z
    unfold residueSmoothWeight
    split
    · exact (smoothProductProfile_range (K × X) _).1
    · exact le_rfl
  · exact tsum_nonneg (selectedResidueSmoothWeight_nonneg modulus T V)

theorem selectedResidueCellWeight_sum (modulus : X → ℕ)
    (T : Finset (ColumnResiduePattern K X modulus)) (V : K × X → ℝ)
    (hV : ∀ z, 0 < V z) (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T V z) :
    (∑ r : T, selectedResidueCellWeight modulus T V r) = 1 := by
  simp only [selectedResidueCellWeight, ← Finset.sum_div]
  rw [← selectedResidueSmoothWeight_mass modulus T V hV, div_self hZ.ne']

theorem selectedResidueSmoothPMF_bounded_mixture (modulus : X → ℕ)
    (hmodulus : ∀ x, 0 < modulus x) (T : Finset (ColumnResiduePattern K X modulus))
    (V : K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T V z)
    (hc : ∀ r : T, 0 < shiftedSmoothProductMass
      (residueProfileCenter (boundedColumnResidueRepresentative modulus r.val) modulus)
      (residueProfileWidth modulus V)) (φ : (K × X → ℤ) → ℂ) :
    (∑' z, ((selectedResidueSmoothPMF modulus T V hV hZ z).toReal : ℂ) * φ z) =
      ∑ r : T, (selectedResidueCellWeight modulus T V r : ℂ) *
        ∑' z, ((residueSmoothPMF (boundedColumnResidueRepresentative modulus r.val)
          modulus hmodulus V hV (hc r) z).toReal : ℂ) * φ z := by
  have hm (r : T) := residueSmoothMass_congr _ _ modulus hmodulus V hV
    (boundedColumnResidueRepresentative_congr modulus r.val)
  have ho (r : T) : 0 < shiftedSmoothProductMass
      (residueProfileCenter (columnResidueRepresentative modulus r.val) modulus)
      (residueProfileWidth modulus V) := by rw [hm r]; exact hc r
  rw [selectedResidueSmoothPMF_mixture modulus hmodulus T V hV hZ ho]
  apply Finset.sum_congr rfl
  intro r _
  rw [residueSmoothPMF_congr _ _ modulus hmodulus V hV
    (boundedColumnResidueRepresentative_congr modulus r.val) (ho r) (hc r)]
  rfl

theorem selectedResidue_bounded_mixture_error (modulus : X → ℕ)
    (hmodulus : ∀ x, 0 < modulus x) (T : Finset (ColumnResiduePattern K X modulus))
    (V : K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T V z)
    (hc : ∀ r : T, 0 < shiftedSmoothProductMass
      (residueProfileCenter (boundedColumnResidueRepresentative modulus r.val) modulus)
      (residueProfileWidth modulus V)) (φ : (K × X → ℤ) → ℂ)
    (target : T → ℂ) (ε : T → ℝ)
    (he : ∀ r : T, ‖(∑' z, ((residueSmoothPMF (boundedColumnResidueRepresentative modulus r.val)
      modulus hmodulus V hV (hc r) z).toReal : ℂ) * φ z) - target r‖ ≤ ε r) :
    ‖(∑' z, ((selectedResidueSmoothPMF modulus T V hV hZ z).toReal : ℂ) * φ z) -
      ∑ r : T, (selectedResidueCellWeight modulus T V r : ℂ) * target r‖ ≤
      ∑ r : T, selectedResidueCellWeight modulus T V r * ε r := by
  rw [selectedResidueSmoothPMF_bounded_mixture modulus hmodulus T V hV hZ hc φ,
    ← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro r _
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (selectedResidueCellWeight_nonneg modulus T V r)]
  exact mul_le_mul_of_nonneg_left (he r) (selectedResidueCellWeight_nonneg modulus T V r)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem residueProfile_center_ratio {K X : Type*}
    (r : K × X → ℤ) (q : X → ℕ) (hq : ∀ x, 0 < q x)
    (V : K × X → ℝ) (hV : ∀ z, 0 < V z) (z : K × X) :
    |residueProfileCenter r q z| / residueProfileWidth q V z = |(r z : ℝ)| / V z := by
  have hq0 : (0 : ℝ) < q z.2 := by exact_mod_cast hq z.2
  simp only [residueProfileCenter, residueProfileWidth, abs_div, abs_neg, abs_of_pos hq0]
  field_simp [hq0.ne', (hV z).ne']

theorem residueSmoothIndexPMF_recenter_test {K X : Type*} [Fintype K] [Fintype X]
    (r : K × X → ℤ) (q : X → ℕ) (hq : ∀ x, 0 < q x)
    (V : K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hc : 0 < shiftedSmoothProductMass (residueProfileCenter r q) (residueProfileWidth q V))
    (hlarge : ∀ z, 8 * (probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth q V z)
    (φ : (K × X → ℤ) → ℂ) {B : ℝ} (hB : 0 ≤ B) (hφ : ∀ z, ‖φ z‖ ≤ B) :
    ‖(∑' z, ((residueSmoothIndexPMF r q hq V hV hc z).toReal : ℂ) * φ z) -
      ∑' z, ((smoothProductPMF (residueProfileWidth q V)
        (residueProfileWidth_pos q V hq hV) z).toReal : ℂ) * φ z‖ ≤
      B * (24 * (probabilityProfileLipschitz : ℝ) * ∑ z, |(r z : ℝ)| / V z) := by
  have h := shiftedSmoothProductPMF_recenter_test (residueProfileCenter r q)
    (residueProfileWidth q V) (residueProfileWidth_pos q V hq hV) hc hlarge φ hB hφ
  simpa only [residueSmoothIndexPMF, residueProfile_center_ratio r q hq V hV] using h

theorem residueSmoothPMF_recenter_test {K X : Type*} [Fintype K] [Fintype X]
    (r : K × X → ℤ) (q : X → ℕ) (hq : ∀ x, 0 < q x)
    (V : K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hc : 0 < shiftedSmoothProductMass (residueProfileCenter r q) (residueProfileWidth q V))
    (hlarge : ∀ z, 8 * (probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth q V z)
    (φ : (K × X → ℤ) → ℂ) {B : ℝ} (hB : 0 ≤ B) (hφ : ∀ z, ‖φ z‖ ≤ B) :
    ‖(∑' z, ((residueSmoothPMF r q hq V hV hc z).toReal : ℂ) * φ z) -
      ∑' z, ((smoothProductPMF (residueProfileWidth q V)
        (residueProfileWidth_pos q V hq hV) z).toReal : ℂ) * φ (residueLatticeArray r q z)‖ ≤
      B * (24 * (probabilityProfileLipschitz : ℝ) * ∑ z, |(r z : ℝ)| / V z) := by
  rw [residueSmoothPMF_expectation]
  exact residueSmoothIndexPMF_recenter_test r q hq V hV hc hlarge
    (fun z => φ (residueLatticeArray r q z)) hB (fun z => hφ _)

theorem boundedResidueSmoothPMF_recenter_test {K X : Type*} [Fintype K] [Fintype X]
    (q : X → ℕ) (hq : ∀ x, 0 < q x) (r : ColumnResiduePattern K X q)
    (V : K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hc : 0 < shiftedSmoothProductMass (residueProfileCenter (boundedColumnResidueRepresentative q r) q)
      (residueProfileWidth q V))
    (hlarge : ∀ z, 8 * (probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth q V z)
    (φ : (K × X → ℤ) → ℂ) {B : ℝ} (hB : 0 ≤ B) (hφ : ∀ z, ‖φ z‖ ≤ B) :
    ‖(∑' z, ((residueSmoothPMF (boundedColumnResidueRepresentative q r) q hq V hV hc z).toReal : ℂ) * φ z) -
      ∑' z, ((smoothProductPMF (residueProfileWidth q V)
        (residueProfileWidth_pos q V hq hV) z).toReal : ℂ) *
          φ (residueLatticeArray (boundedColumnResidueRepresentative q r) q z)‖ ≤
      B * (24 * (probabilityProfileLipschitz : ℝ) * ∑ z : K × X, (q z.2 : ℝ) / V z) := by
  apply (residueSmoothPMF_recenter_test (boundedColumnResidueRepresentative q r) q hq V hV hc
    hlarge φ hB hφ).trans
  apply mul_le_mul_of_nonneg_left _ hB
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro z _
  have hr := boundedColumnResidueRepresentative_bounds q hq r z
  have hr0 : (0 : ℝ) ≤ boundedColumnResidueRepresentative q r z := by exact_mod_cast hr.1
  apply div_le_div_of_nonneg_right _ (hV z).le
  rw [abs_of_nonneg hr0]
  exact_mod_cast hr.2.le

theorem selectedResidueSmoothPMF_recenter_test {K X : Type*} [Fintype K] [Fintype X]
    (q : X → ℕ) (hq : ∀ x, 0 < q x) (T : Finset (ColumnResiduePattern K X q))
    (V : K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight q T V z)
    (hlarge : ∀ z, 8 * (probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth q V z)
    (φ : (K × X → ℤ) → ℂ) {B : ℝ} (hB : 0 ≤ B) (hφ : ∀ z, ‖φ z‖ ≤ B) :
    ‖(∑' z, ((selectedResidueSmoothPMF q T V hV hZ z).toReal : ℂ) * φ z) -
      ∑ r : T, (selectedResidueCellWeight q T V r : ℂ) *
        ∑' z, ((smoothProductPMF (residueProfileWidth q V)
          (residueProfileWidth_pos q V hq hV) z).toReal : ℂ) *
            φ (residueLatticeArray (boundedColumnResidueRepresentative q r.val) q z)‖ ≤
      B * (24 * (probabilityProfileLipschitz : ℝ) * ∑ z : K × X, (q z.2 : ℝ) / V z) := by
  have hc (r : T) := shiftedSmoothProductMass_pos_of_large
    (residueProfileCenter (boundedColumnResidueRepresentative q r.val) q) (residueProfileWidth q V) hlarge
  have h := selectedResidue_bounded_mixture_error q hq T V hV hZ hc φ _
    (fun _ => B * (24 * (probabilityProfileLipschitz : ℝ) * ∑ z : K × X, (q z.2 : ℝ) / V z))
    (fun r => boundedResidueSmoothPMF_recenter_test q hq r.val V hV (hc r) hlarge φ hB hφ)
  simpa only [← Finset.sum_mul, selectedResidueCellWeight_sum q T V hV hZ, one_mul] using h

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

variable {K X Y : Type*} [Fintype K] [Fintype X]

theorem selectedResidueSmoothPMF_bind_toReal_mixture
    (q : X → ℕ) (hq : ∀ x, 0 < q x)
    (T : Finset (ColumnResiduePattern K X q))
    (V : K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight q T V z)
    (hc : ∀ r : T, 0 < shiftedSmoothProductMass
      (residueProfileCenter (boundedColumnResidueRepresentative q r.val) q)
      (residueProfileWidth q V))
    (F : (K × X → ℤ) → PMF Y) (y : Y) :
    (((selectedResidueSmoothPMF q T V hV hZ).bind F) y).toReal =
      ∑ r : T, selectedResidueCellWeight q T V r *
        (((residueSmoothPMF (boundedColumnResidueRepresentative q r.val)
          q hq V hV (hc r)).bind F) y).toReal := by
  apply Complex.ofReal_injective
  simp only [pmf_bind_toReal, Complex.ofReal_tsum, Complex.ofReal_sum, Complex.ofReal_mul]
  exact selectedResidueSmoothPMF_bounded_mixture q hq T V hV hZ hc
    (fun z => ((F z y).toReal : ℂ))

theorem selectedResidueSmoothPMF_bind_le_of_cells
    (q : X → ℕ) (hq : ∀ x, 0 < q x)
    (T : Finset (ColumnResiduePattern K X q))
    (V : K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight q T V z)
    (hc : ∀ r : T, 0 < shiftedSmoothProductMass
      (residueProfileCenter (boundedColumnResidueRepresentative q r.val) q)
      (residueProfileWidth q V))
    (F : (K × X → ℤ) → PMF Y) (y : Y) (δ : ℝ)
    (hbound : ∀ r : T, (((residueSmoothPMF (boundedColumnResidueRepresentative q r.val)
      q hq V hV (hc r)).bind F) y).toReal ≤ δ) :
    (((selectedResidueSmoothPMF q T V hV hZ).bind F) y).toReal ≤ δ := by
  rw [selectedResidueSmoothPMF_bind_toReal_mixture q hq T V hV hZ hc F y]
  calc
    _ ≤ ∑ r : T, selectedResidueCellWeight q T V r * δ :=
      Finset.sum_le_sum (fun r _ => mul_le_mul_of_nonneg_left (hbound r)
        (selectedResidueCellWeight_nonneg q T V r))
    _ = δ := by rw [← Finset.sum_mul, selectedResidueCellWeight_sum q T V hV hZ, one_mul]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {K X : Type*} [Fintype K] [Fintype X]

theorem selectedResidueDensityMass_bounded_mixture
    (modulus : X → ℕ) (hmodulus : ∀ x, 0 < modulus x)
    (T : Finset (ColumnResiduePattern K X modulus))
    (V : K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T V z)
    (hc : ∀ r : T, 0 < shiftedSmoothProductMass
      (residueProfileCenter (boundedColumnResidueRepresentative modulus r.val) modulus)
      (residueProfileWidth modulus V)) (D : (K × X → ℤ) → ℝ) :
    selectedResidueDensityMass modulus T V D =
      ∑ r : T, selectedResidueCellWeight modulus T V r *
        ∑' z, (residueSmoothPMF (boundedColumnResidueRepresentative modulus r.val)
          modulus hmodulus V hV (hc r) z).toReal * D z := by
  apply Complex.ofReal_injective
  rw [selectedResidueDensityMass_complex modulus T V hV hZ D]
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_tsum]
  exact selectedResidueSmoothPMF_bounded_mixture modulus hmodulus T V hV hZ hc
    (fun z => (D z : ℂ))

theorem selectedResidueDensityNumerator_bounded_mixture
    (modulus : X → ℕ) (hmodulus : ∀ x, 0 < modulus x)
    (T : Finset (ColumnResiduePattern K X modulus))
    (V : K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T V z)
    (hc : ∀ r : T, 0 < shiftedSmoothProductMass
      (residueProfileCenter (boundedColumnResidueRepresentative modulus r.val) modulus)
      (residueProfileWidth modulus V))
    (D : (K × X → ℤ) → ℝ) (φ : (K × X → ℤ) → ℂ) :
    (∑' z, ((selectedResidueSmoothPMF modulus T V hV hZ z).toReal : ℂ) *
      ((D z : ℂ) * φ z)) =
      ∑ r : T, (selectedResidueCellWeight modulus T V r : ℂ) *
        ∑' z, ((residueSmoothPMF (boundedColumnResidueRepresentative modulus r.val)
          modulus hmodulus V hV (hc r) z).toReal : ℂ) * ((D z : ℂ) * φ z) :=
  selectedResidueSmoothPMF_bounded_mixture modulus hmodulus T V hV hZ hc
    (fun z => (D z : ℂ) * φ z)

theorem selectedResidueDensityPMF_bounded_mixture_ratio
    (modulus : X → ℕ) (hmodulus : ∀ x, 0 < modulus x)
    (T : Finset (ColumnResiduePattern K X modulus))
    (V : K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T V z)
    (hc : ∀ r : T, 0 < shiftedSmoothProductMass
      (residueProfileCenter (boundedColumnResidueRepresentative modulus r.val) modulus)
      (residueProfileWidth modulus V))
    (D : (K × X → ℤ) → ℝ) (hD0 : ∀ z, 0 ≤ D z)
    (hD : 0 < selectedResidueDensityMass modulus T V D)
    (φ : (K × X → ℤ) → ℂ) :
    (∑' z, ((selectedResidueDensityPMF modulus T V hV hZ D hD0 hD z).toReal : ℂ) * φ z) =
      (∑ r : T, (selectedResidueCellWeight modulus T V r : ℂ) *
        ∑' z, ((residueSmoothPMF (boundedColumnResidueRepresentative modulus r.val)
          modulus hmodulus V hV (hc r) z).toReal : ℂ) * ((D z : ℂ) * φ z)) /
      ((∑ r : T, selectedResidueCellWeight modulus T V r *
        ∑' z, (residueSmoothPMF (boundedColumnResidueRepresentative modulus r.val)
          modulus hmodulus V hV (hc r) z).toReal * D z : ℝ) : ℂ) := by
  rw [selectedResidueDensityPMF_complexMean,
    selectedResidueDensityNumerator_bounded_mixture modulus hmodulus T V hV hZ hc,
    selectedResidueDensityMass_bounded_mixture modulus hmodulus T V hV hZ hc]

theorem selectedResidueSmoothWeight_singleton
    (modulus : X → ℕ) (r : ColumnResiduePattern K X modulus)
    (V : K × X → ℝ) (z : K × X → ℤ) :
    selectedResidueSmoothWeight modulus {r} V z =
      residueSmoothWeight (columnResidueRepresentative modulus r) modulus V z := by
  simp only [selectedResidueSmoothWeight, Finset.mem_singleton, residueSmoothWeight_eq_pattern]

theorem selectedResidueSmoothWeight_mass_pos_of_singletons
    (modulus : X → ℕ) (T : Finset (ColumnResiduePattern K X modulus))
    (hT : T.Nonempty) (V : K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hcellZ : ∀ r : T, 0 < ∑' z, selectedResidueSmoothWeight modulus {r.val} V z) :
    0 < ∑' z, selectedResidueSmoothWeight modulus T V z := by
  apply selectedResidueSmoothWeight_mass_pos modulus T hT V hV
  intro r
  simpa only [selectedResidueSmoothWeight_singleton] using hcellZ r

theorem selectedResidueSmoothPMF_singleton_mixture
    (modulus : X → ℕ) (T : Finset (ColumnResiduePattern K X modulus))
    (V : K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T V z)
    (hcellZ : ∀ r : T, 0 < ∑' z, selectedResidueSmoothWeight modulus {r.val} V z)
    (φ : (K × X → ℤ) → ℂ) :
    (∑' z, ((selectedResidueSmoothPMF modulus T V hV hZ z).toReal : ℂ) * φ z) =
      ∑ r : T, (selectedResidueCellWeight modulus T V r : ℂ) *
        ∑' z, ((selectedResidueSmoothPMF modulus {r.val} V hV (hcellZ r) z).toReal : ℂ) * φ z := by
  have hcell (r : T) :
      0 < ∑' z, residueSmoothWeight (columnResidueRepresentative modulus r.val) modulus V z := by
    simpa only [selectedResidueSmoothWeight_singleton] using hcellZ r
  have ht := selectedResidueSmoothWeight_mass modulus T V hV
  have htotal : 0 < ∑ r : T, ∑' z,
      residueSmoothWeight (columnResidueRepresentative modulus r.val) modulus V z := by
    rwa [← ht]
  simp only [selectedResidueSmoothPMF_toReal]
  simp only [selectedResidueSmoothWeight_singleton, selectedResidueCellWeight]
  simp only [ht]
  simp only [selectedResidueSmoothWeight_eq_sum]
  exact finite_supported_normalized_mixture _ (rectangularWeightIndices 0 V 1)
    (fun r => residueSmoothWeight_zero_off _ modulus V hV) hcell htotal φ

theorem selectedResidueDensityMass_singleton_mixture
    (modulus : X → ℕ) (T : Finset (ColumnResiduePattern K X modulus))
    (V : K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T V z)
    (hcellZ : ∀ r : T, 0 < ∑' z, selectedResidueSmoothWeight modulus {r.val} V z)
    (D : (K × X → ℤ) → ℝ) :
    selectedResidueDensityMass modulus T V D =
      ∑ r : T, selectedResidueCellWeight modulus T V r *
        selectedResidueDensityMass modulus {r.val} V D := by
  apply Complex.ofReal_injective
  rw [selectedResidueDensityMass_complex modulus T V hV hZ D]
  simp only [Complex.ofReal_sum, Complex.ofReal_mul]
  simp_rw [selectedResidueDensityMass_complex modulus _ V hV (hcellZ _) D]
  exact selectedResidueSmoothPMF_singleton_mixture modulus T V hV hZ hcellZ
    (fun z => (D z : ℂ))

theorem selectedResidueDensityNumerator_singleton_mixture
    (modulus : X → ℕ) (T : Finset (ColumnResiduePattern K X modulus))
    (V : K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T V z)
    (hcellZ : ∀ r : T, 0 < ∑' z, selectedResidueSmoothWeight modulus {r.val} V z)
    (D : (K × X → ℤ) → ℝ) (φ : (K × X → ℤ) → ℂ) :
    (∑' z, ((selectedResidueSmoothPMF modulus T V hV hZ z).toReal : ℂ) *
      ((D z : ℂ) * φ z)) =
      ∑ r : T, (selectedResidueCellWeight modulus T V r : ℂ) *
        ∑' z, ((selectedResidueSmoothPMF modulus {r.val} V hV (hcellZ r) z).toReal : ℂ) *
          ((D z : ℂ) * φ z) :=
  selectedResidueSmoothPMF_singleton_mixture modulus T V hV hZ hcellZ
    (fun z => (D z : ℂ) * φ z)

theorem selectedResidueDensityPMF_singleton_mixture_ratio
    (modulus : X → ℕ) (T : Finset (ColumnResiduePattern K X modulus))
    (V : K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T V z)
    (hcellZ : ∀ r : T, 0 < ∑' z, selectedResidueSmoothWeight modulus {r.val} V z)
    (D : (K × X → ℤ) → ℝ) (hD0 : ∀ z, 0 ≤ D z)
    (hD : 0 < selectedResidueDensityMass modulus T V D)
    (φ : (K × X → ℤ) → ℂ) :
    (∑' z, ((selectedResidueDensityPMF modulus T V hV hZ D hD0 hD z).toReal : ℂ) * φ z) =
      (∑ r : T, (selectedResidueCellWeight modulus T V r : ℂ) *
        ∑' z, ((selectedResidueSmoothPMF modulus {r.val} V hV (hcellZ r) z).toReal : ℂ) *
          ((D z : ℂ) * φ z)) /
      ((∑ r : T, selectedResidueCellWeight modulus T V r *
        selectedResidueDensityMass modulus {r.val} V D : ℝ) : ℂ) := by
  rw [selectedResidueDensityPMF_complexMean,
    selectedResidueDensityNumerator_singleton_mixture modulus T V hV hZ hcellZ,
    selectedResidueDensityMass_singleton_mixture modulus T V hV hZ hcellZ]

theorem selectedResidueDensityPMF_singleton_mixture_error
    (modulus : X → ℕ) (T : Finset (ColumnResiduePattern K X modulus))
    (V : K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T V z)
    (hcellZ : ∀ r : T, 0 < ∑' z, selectedResidueSmoothWeight modulus {r.val} V z)
    (D : (K × X → ℤ) → ℝ) (hD0 : ∀ z, 0 ≤ D z)
    (hD : 0 < selectedResidueDensityMass modulus T V D)
    (φ : (K × X → ℤ) → ℂ) (target : T → ℂ) {E γ : ℝ}
    (hγ : γ ≤ 1 / 2)
    (hraw : ∀ r : T,
      ‖(∑' z, ((selectedResidueSmoothPMF modulus {r.val} V hV (hcellZ r) z).toReal : ℂ) *
        ((D z : ℂ) * φ z)) - target r‖ ≤ E)
    (hmass : ∀ r : T, |selectedResidueDensityMass modulus {r.val} V D - 1| ≤ γ)
    (htarget : ∀ r : T, ‖target r‖ ≤ 1) :
    ‖(∑' z, ((selectedResidueDensityPMF modulus T V hV hZ D hD0 hD z).toReal : ℂ) * φ z) -
      ∑ r : T, (selectedResidueCellWeight modulus T V r : ℂ) * target r‖ ≤ 2 * E + 2 * γ := by
  have hweights := selectedResidueCellWeight_sum modulus T V hV hZ
  have hnonneg := selectedResidueCellWeight_nonneg modulus T V
  have hmass_global : |selectedResidueDensityMass modulus T V D - 1| ≤ γ := by
    have heq : selectedResidueDensityMass modulus T V D - 1 =
        ∑ r : T, selectedResidueCellWeight modulus T V r *
          (selectedResidueDensityMass modulus {r.val} V D - 1) := by
      simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hweights]
      rw [selectedResidueDensityMass_singleton_mixture modulus T V hV hZ hcellZ]
    rw [heq]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ r : T, selectedResidueCellWeight modulus T V r * γ := by
        apply Finset.sum_le_sum
        intro r _
        rw [abs_mul, abs_of_nonneg (hnonneg r)]
        exact mul_le_mul_of_nonneg_left (hmass r) (hnonneg r)
      _ = γ := by rw [← Finset.sum_mul, hweights, one_mul]
  have hlower : 1 / 2 ≤ selectedResidueDensityMass modulus T V D := by
    have := (abs_le.mp hmass_global).1
    linarith
  have hraw_global :
      ‖(∑' z, ((selectedResidueSmoothPMF modulus T V hV hZ z).toReal : ℂ) *
        ((D z : ℂ) * φ z)) -
        ∑ r : T, (selectedResidueCellWeight modulus T V r : ℂ) * target r‖ ≤ E := by
    rw [selectedResidueDensityNumerator_singleton_mixture modulus T V hV hZ hcellZ,
      ← Finset.sum_sub_distrib]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ r : T, selectedResidueCellWeight modulus T V r * E := by
        apply Finset.sum_le_sum
        intro r _
        rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hnonneg r)]
        exact mul_le_mul_of_nonneg_left (hraw r) (hnonneg r)
      _ = E := by rw [← Finset.sum_mul, hweights, one_mul]
  have htarget_global :
      ‖∑ r : T, (selectedResidueCellWeight modulus T V r : ℂ) * target r‖ ≤ 1 := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ r : T, selectedResidueCellWeight modulus T V r * 1 := by
        apply Finset.sum_le_sum
        intro r _
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hnonneg r)]
        exact mul_le_mul_of_nonneg_left (htarget r) (hnonneg r)
      _ = 1 := by simpa only [mul_one] using hweights
  simpa only [mul_one] using selectedResidueDensityPMF_error modulus T V hV hZ D hD0 hD φ
    hlower hraw_global hmass_global htarget_global

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem selectedResidueSmoothPMF_singleton_residue_mean
    {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (r : ColumnResiduePattern K I modulus)
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus {r} V z)
    (F : ColumnResiduePattern K I modulus → ℂ) :
    (∑' z, ((selectedResidueSmoothPMF modulus {r} V hV hZ z).toReal : ℂ) *
      F (columnResiduePattern modulus z)) = F r := by
  have hp : (∑' z, (selectedResidueSmoothPMF modulus {r} V hV hZ z).toReal) = 1 := by
    rw [← ENNReal.tsum_toReal_eq (fun z => PMF.apply_ne_top _ z), PMF.tsum_coe,
      ENNReal.toReal_one]
  calc
    _ = ∑' z, ((selectedResidueSmoothPMF modulus {r} V hV hZ z).toReal : ℂ) * F r := by
      apply tsum_congr
      intro z
      by_cases hz : columnResiduePattern modulus z = r
      · rw [hz]
      · simp only [selectedResidueSmoothPMF_toReal, selectedResidueSmoothWeight,
          Finset.mem_singleton, hz, ite_false, zero_div, Complex.ofReal_zero, zero_mul]
    _ = (∑' z, ((selectedResidueSmoothPMF modulus {r} V hV hZ z).toReal : ℂ)) * F r :=
      tsum_mul_right
    _ = F r := by rw [← Complex.ofReal_tsum, hp, Complex.ofReal_one, one_mul]

theorem selectedResidueRefinement_weighted_mean
    {K I : Type*} [Fintype K] [Fintype I]
    (modulus refined : I → ℕ) [∀ i, NeZero (refined i)]
    (hdiv : ∀ i, modulus i ∣ refined i) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus G V z)
    (hcellZ : ∀ r : selectedResidueRefinement modulus refined hdiv G,
      0 < ∑' z, selectedResidueSmoothWeight refined {r.val} V z)
    (F : ColumnResiduePattern K I refined → ℂ) :
    (∑ r : selectedResidueRefinement modulus refined hdiv G,
      (selectedResidueCellWeight refined (selectedResidueRefinement modulus refined hdiv G) V r : ℂ) *
        F r.val) =
      ∑' z, ((selectedResidueSmoothPMF modulus G V hV hZ z).toReal : ℂ) *
        F (columnResiduePattern refined z) := by
  have hZref : 0 < ∑' z, selectedResidueSmoothWeight refined
      (selectedResidueRefinement modulus refined hdiv G) V z := by
    rw [selectedResidueSmoothMass_refinement]
    exact hZ
  have h := selectedResidueSmoothPMF_singleton_mixture refined
    (selectedResidueRefinement modulus refined hdiv G) V hV hZref hcellZ
    (fun z => F (columnResiduePattern refined z))
  rw [selectedResidueSmoothPMF_refinement modulus refined hdiv G V hV hZ hZref] at h
  simp only [selectedResidueSmoothPMF_singleton_residue_mean] at h
  exact h.symm

end Erdos3

end

end OAI
