import OAI.Combinatorics.Progressions.Estimates.AllocatedCoveredSiteExpansion
import OAI.Combinatorics.Progressions.Estimates.AllocatedFullSiteRadius
import OAI.Combinatorics.Progressions.Linear.BufferedCoordinateProjection

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module
open scoped Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

noncomputable def allocatedFullMixedSiteValue
    (w : ∀ j : Fin m, (I j → ℝ) × (Fin (n j) → ℤ)) : LayerSamplerAxis I n → ℝ
  | ⟨j, .inl i⟩ => (w j).1 i / R j
  | ⟨j, .inr i⟩ => ((w j).2 i : ℝ) / (basisAxisScale (b j) i : ℝ) / R j

theorem allocatedFullMixedSiteValue_projection
    (w : ∀ j : Fin m, (I j → ℝ) × (Fin (n j) → ℤ)) :
    coordinateZeroProjection (allocatedGridAxis (I := I) U b S.value)
      (allocatedFullMixedSiteValue (R := R) U b w) = allocatedNormalizedMixedSiteValue B U b S w := by
  funext a
  rcases a with ⟨j, i | i⟩ <;> rfl

omit [∀ j, Fintype (I j)] in
theorem allocatedFullMixedSiteValue_continuous :
    Continuous (allocatedFullMixedSiteValue (I := I) (R := R) U b) := by
  apply continuous_pi
  rintro ⟨j, i | i⟩
  · change Continuous (fun w : ∀ j : Fin m, (I j → ℝ) × (Fin (n j) → ℤ) => (w j).1 i / R j)
    fun_prop
  · change Continuous (fun w : ∀ j : Fin m, (I j → ℝ) × (Fin (n j) → ℤ) =>
      ((w j).2 i : ℝ) / (basisAxisScale (b j) i : ℝ) / R j)
    fun_prop

theorem allocatedFullMixedSiteValue_point_bound
    (hR : ∀ j, 0 < R j) (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (w : ∀ j : Fin m, (I j → ℝ) × (Fin (n j) → ℤ))
    {r : ℝ} (hr : 0 ≤ r) (hw : ∀ a, |allocatedFullMixedSiteValue (R := R) U b w a| ≤ r)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (j : Fin m) :
    ‖normalizedLatticePoint (euclideanSubspace (U j)) (b j) (orthonormalMixedChart (o j) (w j))‖ ≤
      C j * (((Fintype.card (I j) : ℝ) + 1) * (r * R j)) := by
  have hreal (i : I j) : |(w j).1 i| ≤ r * R j := by
    have h := hw ⟨j, Sum.inl i⟩
    change |(w j).1 i / R j| ≤ r at h
    rw [abs_div, abs_of_pos (hR j)] at h
    exact (div_le_iff₀ (hR j)).mp h
  have hint (i : Fin (n j)) : |((w j).2 i : ℝ) / basisAxisScale (b j) i| ≤ r * R j := by
    have h := hw ⟨j, Sum.inr i⟩
    change |((w j).2 i : ℝ) / basisAxisScale (b j) i / R j| ≤ r at h
    rw [abs_div, abs_of_pos (hR j)] at h
    exact (div_le_iff₀ (hR j)).mp h
  exact mixedRealPoint_norm_le (euclideanSubspace (U j)) (b j) (o j) (hC j)
    (mul_nonneg hr (hR j).le) (hchart j) (w j).1
    (fun i => ((w j).2 i : ℝ) / basisAxisScale (b j) i) hreal hint

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "single" => (fun _ : Fin m => Unit)
local notation "quarter" => (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))
local notation "chart" => mixedCoveredJetChart (O := single) U o b hb bW d
local notation "region" => mixedCoveredJetRegion (O := single) (E := Q) U o b d quarter

noncomputable def allocatedIdealSiteChartFactor (f : (LayerSamplerAxis I n → ℝ) → ℂ) :
    EuclideanJetLayers U single → ℂ :=
  restrictedComplexChartDensity chart region 1 (fun z =>
    f (allocatedNormalizedMixedSiteValue B U b S
      (fun j => mixedArrayRegroup _ _ _ (z.1 j) ())))

theorem allocatedIdealSiteChartFactor_norm_le
    (f : (LayerSamplerAxis I n → ℝ) → ℂ) {C : ℝ} (hC : 0 ≤ C) (hf : ∀ v, ‖f v‖ ≤ C)
    (y : EuclideanJetLayers U single) : ‖allocatedIdealSiteChartFactor B U b S o hb bW d f y‖ ≤ C := by
  by_cases hy : y ∈ chart '' region
  · obtain ⟨z, hz, rfl⟩ := hy
    rw [allocatedIdealSiteChartFactor, restrictedComplexChartDensity_apply _ _ _ _
      (mixedCoveredJetChart_injOn U o b hb bW d quarter
        (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))) hz,
      Complex.ofReal_one, one_mul]
    exact hf _
  · rw [allocatedIdealSiteChartFactor, restrictedComplexChartDensity_zero _ _ _ _ hy, norm_zero]
    exact hC

variable {α : Type*} [Fintype α] [DecidableEq α]

local notation "jets" => (fun j : Fin m => BoundedBooleanJet α ((j : ℕ) + 1))
local notation "grid" => allocatedGridAxis (I := I) U b S.value

theorem allocatedIdealSiteChartFactor_apply
    (f : (LayerSamplerAxis I n → ℝ) → ℂ) (z : MixedCoveredJetSource I jets Q n d)
    (s : Finset α) (hs : mixedCoveredBooleanSiteValue d z s ∈ region) :
    allocatedIdealSiteChartFactor B U b S o hb bW d f
        (coveredBooleanSiteValue U (mixedCoveredJetChart U o b hb bW d z) s) =
      f (allocatedIdealSiteCoordinates B U b S ((coefficientJetAxisSplit jets I n grid z.1).2) s) := by
  rw [← mixedCoveredBooleanSiteValue_chart U o b hb bW d z s]
  rw [allocatedIdealSiteChartFactor, restrictedComplexChartDensity_apply _ _ _ _
    (mixedCoveredJetChart_injOn U o b hb bW d quarter
      (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))) hs,
    Complex.ofReal_one, one_mul]
  change f (allocatedNormalizedMixedSiteValue B U b S (mixedBooleanSiteValue z.1 s)) = _
  rw [allocatedIdealSiteCoordinates_mixed_value]

theorem allocatedIdealSiteChartFactor_product
    (f : Finset α → (LayerSamplerAxis I n → ℝ) → ℂ)
    (z : MixedCoveredJetSource I jets Q n d)
    (hs : ∀ s, mixedCoveredBooleanSiteValue d z s ∈ region) :
    (∏ s, allocatedIdealSiteChartFactor B U b S o hb bW d (f s)
      (coveredBooleanSiteValue U (mixedCoveredJetChart U o b hb bW d z) s)) =
    ∏ s, f s (allocatedIdealSiteCoordinates B U b S ((coefficientJetAxisSplit jets I n grid z.1).2) s) := by
  exact Finset.prod_congr rfl (fun s _ => allocatedIdealSiteChartFactor_apply B U b S o hb bW d (f s) z s (hs s))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module
open scoped Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (r : ℝ≥0) (hr : 0 < r) (f : (LayerSamplerAxis I n → ℝ) → ℂ)

noncomputable def allocatedBufferedMixedSiteFactor
    (w : ∀ j : Fin m, (I j → ℝ) × (Fin (n j) → ℤ)) : ℂ :=
  bufferedCoordinateProjection (allocatedGridAxis (I := I) U b S.value) r hr f
    (allocatedFullMixedSiteValue (R := R) U b w)

theorem allocatedBufferedMixedSiteFactor_norm_le (hf : ∀ z, ‖f z‖ ≤ 1)
    (w : ∀ j : Fin m, (I j → ℝ) × (Fin (n j) → ℤ)) :
    ‖allocatedBufferedMixedSiteFactor B U b S r hr f w‖ ≤ 1 :=
  bufferedCoordinateProjection_norm_le _ r hr f hf _

theorem allocatedBufferedMixedSiteFactor_continuous {L : ℝ≥0}
    (hf : LipschitzWith L f) (hf1 : ∀ z, ‖f z‖ ≤ 1) :
    Continuous (allocatedBufferedMixedSiteFactor B U b S r hr f) :=
  (bufferedCoordinateProjection_lipschitz _ r hr f hf hf1).continuous.comp
    (allocatedFullMixedSiteValue_continuous (I := I) (R := R) U b)

theorem allocatedBufferedMixedSiteFactor_eq
    (w : ∀ j : Fin m, (I j → ℝ) × (Fin (n j) → ℤ))
    (hw : ∀ a, |allocatedFullMixedSiteValue (R := R) U b w a| ≤ (r : ℝ)) :
    allocatedBufferedMixedSiteFactor B U b S r hr f w =
      f (allocatedNormalizedMixedSiteValue B U b S w) := by
  rw [allocatedBufferedMixedSiteFactor, bufferedCoordinateProjection_eq _ r hr f _ hw,
    allocatedFullMixedSiteValue_projection]

theorem allocatedBufferedMixedSiteFactor_nonzero_point_bound
    (hR : ∀ j, 0 < R j) (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (w : ∀ j : Fin m, (I j → ℝ) × (Fin (n j) → ℤ))
    (hw : allocatedBufferedMixedSiteFactor B U b S r hr f w ≠ 0)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (j : Fin m) :
    ‖normalizedLatticePoint (euclideanSubspace (U j)) (b j) (orthonormalMixedChart (o j) (w j))‖ ≤
      C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) := by
  exact allocatedFullMixedSiteValue_point_bound U b hR o w
    (mul_nonneg (by norm_num) r.coe_nonneg)
    (bufferedCoordinateProjection_nonzero_box _ r hr f _ hw) C hC hchart j

theorem allocatedBufferedMixedSiteFactor_nonzero_mem_quarter
    (hR : ∀ j, 0 < R j) (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {Q : Fin m → Type*} (d : ℕ)
    (z : MixedCoveredJetSource I (fun _ => Unit) Q n d)
    (hz : allocatedBufferedMixedSiteFactor B U b S r hr f
      (fun j => mixedArrayRegroup _ _ _ (z.1 j) ()) ≠ 0)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4) :
    z ∈ mixedCoveredJetRegion U o b d (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j)) := by
  intro j _ t _
  refine ⟨?_, Set.mem_univ _⟩
  intro i
  cases t
  have h := (allocatedBufferedMixedSiteFactor_nonzero_point_bound B U b S r hr f
    hR o (fun j => mixedArrayRegroup _ _ _ (z.1 j) ()) hz C hC hchart j).trans (hbudget j)
  exact (PiLp.norm_apply_le (normalizedLatticePoint (euclideanSubspace (U j)) (b j)
    (orthonormalMixedChart (o j) (mixedArrayRegroup _ _ _ (z.1 j) ()))) i).trans h

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R : Fin m → ℝ}

local notation "single" => (fun _ : Fin m => Unit)
local notation "ambient" => JetAmbientIndex single J

noncomputable def allocatedFullAmbientSiteCoordinates (z : ambient → ℝ) : LayerSamplerAxis I n → ℝ :=
  fun a =>
    let w := mixedRealCoordinates (euclideanSubspace (U a.1)) (b a.1) (o a.1)
      ((EuclideanSpace.equiv (J a.1) ℝ).symm (fun k => z ⟨a.1, (), k⟩))
    Sum.elim w.1 w.2 a.2 / R a.1

theorem allocatedFullAmbientSiteCoordinates_point
    (z : ∀ j, (I j → Unit → ℝ) × (Fin (n j) → Unit → ℤ)) :
    allocatedFullAmbientSiteCoordinates (R := R) U b o (mixedJetAmbientPoint U b o z) =
      allocatedFullMixedSiteValue (R := R) U b (fun j => mixedArrayRegroup _ _ _ (z j) ()) := by
  have hp (j : Fin m) : (EuclideanSpace.equiv (J j) ℝ).symm
      (fun k => mixedJetAmbientPoint U b o z ⟨j, (), k⟩) =
      normalizedLatticePoint (euclideanSubspace (U j)) (b j)
        (orthonormalMixedChart (o j) (mixedArrayRegroup _ _ _ (z j) ())) := by
    have hv : (fun k => mixedJetAmbientPoint U b o z ⟨j, (), k⟩) =
        (EuclideanSpace.equiv (J j) ℝ) (normalizedLatticePoint (euclideanSubspace (U j)) (b j)
          (orthonormalMixedChart (o j) (mixedArrayRegroup _ _ _ (z j) ()))) := by
      funext k
      rfl
    rw [hv, ContinuousLinearEquiv.symm_apply_apply]
  funext a
  rcases a with ⟨j, i | i⟩ <;>
    dsimp only [allocatedFullAmbientSiteCoordinates, allocatedFullMixedSiteValue] <;>
    rw [hp, mixedRealCoordinates_integer] <;> rfl

theorem allocatedFullAmbientSiteCoordinates_lipschitz (hR : ∀ j, 0 < R j)
    (C : Fin m → ℝ≥0)
    (hC : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ C j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K) :
    LipschitzWith (K * ∑ j, C j * Fintype.card (J j))
      (allocatedFullAmbientSiteCoordinates (R := R) U b o) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  apply (dist_pi_le_iff (by positivity)).mpr
  intro a
  let pz := mixedRealCoordinates (euclideanSubspace (U a.1)) (b a.1) (o a.1)
    ((EuclideanSpace.equiv (J a.1) ℝ).symm (fun k => z ⟨a.1, (), k⟩))
  let pw := mixedRealCoordinates (euclideanSubspace (U a.1)) (b a.1) (o a.1)
    ((EuclideanSpace.equiv (J a.1) ℝ).symm (fun k => w ⟨a.1, (), k⟩))
  have hout : dist (Sum.elim pz.1 pz.2 a.2) (Sum.elim pw.1 pw.2 a.2) ≤ dist pz pw := by
    rcases a.2 with i | i
    · exact (dist_le_pi_dist pz.1 pw.1 i).trans (le_max_left _ _)
    · exact (dist_le_pi_dist pz.2 pw.2 i).trans (le_max_right _ _)
  have hrow := ((mixedRealCoordinates_lipschitz (euclideanSubspace (U a.1)) (b a.1) (o a.1) (hC a.1)).comp
    (euclideanFromCoordinates_lipschitz (D := J a.1))).dist_le_mul
      (fun k => z ⟨a.1, (), k⟩) (fun k => w ⟨a.1, (), k⟩)
  have hin : dist (fun k => z ⟨a.1, (), k⟩) (fun k => w ⟨a.1, (), k⟩) ≤ dist z w :=
    (dist_pi_le_iff dist_nonneg).mpr (fun k => dist_le_pi_dist z w ⟨a.1, (), k⟩)
  have hc : C a.1 * Fintype.card (J a.1) ≤ ∑ j, C j * Fintype.card (J j) :=
    Finset.single_le_sum (f := fun j => C j * Fintype.card (J j))
      (fun _ _ => by positivity) (Finset.mem_univ a.1)
  have hd : dist (Sum.elim pz.1 pz.2 a.2) (Sum.elim pw.1 pw.2 a.2) ≤
      ((∑ j, C j * Fintype.card (J j) : ℝ≥0) : ℝ) * dist z w :=
    (hout.trans hrow).trans ((mul_le_mul_of_nonneg_left hin (NNReal.coe_nonneg _)).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hc) dist_nonneg))
  change |Sum.elim pz.1 pz.2 a.2 / R a.1 - Sum.elim pw.1 pw.2 a.2 / R a.1| ≤ _
  rw [← sub_div, abs_div, abs_of_pos (hR a.1)]
  calc
    _ ≤ (((∑ j, C j * Fintype.card (J j) : ℝ≥0) : ℝ) * dist z w) / R a.1 :=
      div_le_div_of_nonneg_right hd (hR a.1).le
    _ = (R a.1)⁻¹ * (((∑ j, C j * Fintype.card (J j) : ℝ≥0) : ℝ) * dist z w) := by ring
    _ ≤ (K : ℝ) * (((∑ j, C j * Fintype.card (J j) : ℝ≥0) : ℝ) * dist z w) :=
      mul_le_mul_of_nonneg_right (hK a.1) (mul_nonneg (NNReal.coe_nonneg _) dist_nonneg)
    _ = _ := by rw [NNReal.coe_mul, mul_assoc]

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
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r)

local notation "single" => (fun _ : Fin m => Unit)
local notation "quarter" => (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))
local notation "chart" => mixedCoveredJetChart (O := single) U o b hb bW d
local notation "region" => mixedCoveredJetRegion (O := single) (E := Q) U o b d quarter

noncomputable def allocatedBufferedSiteChartFactor (f : (LayerSamplerAxis I n → ℝ) → ℂ) :
    EuclideanJetLayers U single → ℂ :=
  restrictedComplexChartDensity chart region 1 (fun z =>
    allocatedBufferedMixedSiteFactor B U b S r hr f (fun j => mixedArrayRegroup _ _ _ (z.1 j) ()))

theorem allocatedBufferedSiteChartFactor_norm_le
    (f : (LayerSamplerAxis I n → ℝ) → ℂ) (hf : ∀ v, ‖f v‖ ≤ 1)
    (y : EuclideanJetLayers U single) : ‖allocatedBufferedSiteChartFactor B U b S o hb bW d r hr f y‖ ≤ 1 :=
  restrictedComplexChartDensity_norm_le chart region
    (mixedCoveredJetChart_injOn U o b hb bW d quarter
      (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))) _ zero_le_one
    (fun _ => allocatedBufferedMixedSiteFactor_norm_le B U b S r hr f hf _) y

theorem allocatedBufferedSiteChartFactor_measurable
    (f : (LayerSamplerAxis I n → ℝ) → ℂ) {L : ℝ≥0}
    (hf : LipschitzWith L f) (hf1 : ∀ v, ‖f v‖ ≤ 1) :
    Measurable (allocatedBufferedSiteChartFactor B U b S o hb bW d r hr f) := by
  apply mixedCoveredJet_restrictedComplexDensity_measurable U o b hb bW d quarter
    (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))
    (fun j _ => (standardLatticeClosedQuarterBox_isCompact (J j)).isClosed.measurableSet)
  let : ∀ j, BorelSpace ((I j → ℝ) × (Fin (n j) → ℤ)) := fun _ => inferInstance
  let : BorelSpace (∀ j, (I j → ℝ) × (Fin (n j) → ℤ)) := Pi.borelSpace
  apply (allocatedBufferedMixedSiteFactor_continuous B U b S r hr f hf hf1).measurable.comp
  change Measurable (fun z : MixedCoveredJetSource I single Q n d =>
    fun j => ((fun i => (z.1 j).1 i ()), (fun i => (z.1 j).2 i ())))
  fun_prop

theorem allocatedBufferedSiteChartFactor_enlarge
    (f : (LayerSamplerAxis I n → ℝ) → ℂ) (hR : ∀ j, 0 < R j)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)
    (Ω : ∀ j, Unit → Set (EuclideanSpace ℝ (J j)))
    (hquarter : ∀ j t, standardLatticeClosedQuarterBox (J j) ⊆ Ω j t)
    (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j)) :
    allocatedBufferedSiteChartFactor B U b S o hb bW d r hr f =
      restrictedComplexChartDensity chart (mixedCoveredJetRegion U o b d Ω) 1 (fun z =>
        allocatedBufferedMixedSiteFactor B U b S r hr f (fun j => mixedArrayRegroup _ _ _ (z.1 j) ())) := by
  apply restrictedComplexChartDensity_enlarge chart region _
    (mixedCoveredJetRegion_mono U o b d hquarter) (mixedCoveredJetChart_injOn U o b hb bW d Ω hΩ)
  intro z hz
  exact allocatedBufferedMixedSiteFactor_nonzero_mem_quarter B U b S r hr f hR o d z hz C hC hchart hbudget

variable {α : Type*} [Fintype α] [DecidableEq α]

local notation "jets" => (fun j : Fin m => BoundedBooleanJet α ((j : ℕ) + 1))
local notation "grid" => allocatedGridAxis (I := I) U b S.value

theorem allocatedBufferedSiteChartFactor_apply
    (f : (LayerSamplerAxis I n → ℝ) → ℂ) (z : MixedCoveredJetSource I jets Q n d)
    (s : Finset α) (hs : mixedCoveredBooleanSiteValue d z s ∈ region)
    (hbox : ∀ a, |allocatedFullMixedSiteValue (R := R) U b (mixedBooleanSiteValue z.1 s) a| ≤ (r : ℝ)) :
    allocatedBufferedSiteChartFactor B U b S o hb bW d r hr f
        (coveredBooleanSiteValue U (mixedCoveredJetChart U o b hb bW d z) s) =
      f (allocatedIdealSiteCoordinates B U b S ((coefficientJetAxisSplit jets I n grid z.1).2) s) := by
  rw [← mixedCoveredBooleanSiteValue_chart U o b hb bW d z s]
  rw [allocatedBufferedSiteChartFactor, restrictedComplexChartDensity_apply _ _ _ _
    (mixedCoveredJetChart_injOn U o b hb bW d quarter
      (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))) hs,
    Complex.ofReal_one, one_mul]
  change allocatedBufferedMixedSiteFactor B U b S r hr f (mixedBooleanSiteValue z.1 s) = _
  rw [allocatedBufferedMixedSiteFactor_eq B U b S r hr f _ hbox,
    allocatedIdealSiteCoordinates_mixed_value]

theorem allocatedBufferedSiteChartFactor_product
    (f : Finset α → (LayerSamplerAxis I n → ℝ) → ℂ) (z : MixedCoveredJetSource I jets Q n d)
    (hs : ∀ s, mixedCoveredBooleanSiteValue d z s ∈ region)
    (hbox : ∀ s a, |allocatedFullMixedSiteValue (R := R) U b (mixedBooleanSiteValue z.1 s) a| ≤ (r : ℝ)) :
    (∏ s, allocatedBufferedSiteChartFactor B U b S o hb bW d r hr (f s)
      (coveredBooleanSiteValue U (mixedCoveredJetChart U o b hb bW d z) s)) =
      ∏ s, f s (allocatedIdealSiteCoordinates B U b S ((coefficientJetAxisSplit jets I n grid z.1).2) s) := by
  exact Finset.prod_congr rfl (fun s _ => allocatedBufferedSiteChartFactor_apply B U b S o hb bW d r hr
    (f s) z s (hs s) (hbox s))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module
open scoped NNReal

variable {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]

def singleSiteFromLayered (v : (Σ j, J j) → ℝ) :
    JetAmbientIndex (fun _ : Fin m => Unit) J → ℝ := fun a => v ⟨a.1, a.2.2⟩

theorem singleSiteFromLayered_lipschitz : LipschitzWith 1 (singleSiteFromLayered (J := J)) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  simp only [NNReal.coe_one, one_mul]
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro a
  exact dist_le_pi_dist v w ⟨a.1, a.2.2⟩

variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R : Fin m → ℝ}

theorem allocatedFullAmbientSiteCoordinates_layered_point
    (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)) :
    allocatedFullAmbientSiteCoordinates (R := R) U b o
      (singleSiteFromLayered (fun a : Σ j, J j =>
        normalizedLatticePoint (euclideanSubspace (U a.1)) (b a.1) (orthonormalMixedChart (o a.1) (w a.1)) a.2)) =
      allocatedFullMixedSiteValue (R := R) U b w := by
  let z := fun j => ((fun i (_ : Unit) => (w j).1 i), (fun i (_ : Unit) => (w j).2 i))
  change allocatedFullAmbientSiteCoordinates (R := R) U b o (mixedJetAmbientPoint U b o z) = _
  rw [allocatedFullAmbientSiteCoordinates_point]
  rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a) (allocatedPrincipalSides B U b S))

local notation "jets" => (fun j : Fin m => BoundedBooleanJet α ((j : ℕ) + 1))
local notation "rows" => (fun j : Fin m => (Subtype.val : jets j → Finset α))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit jets I n grid

theorem allocatedSiteBox_full_site_bound (hσ1 : ∀ j, σ j ≤ 1)
    (z : ∀ j, (I j → jets j → ℝ) × (Fin (n j) → jets j → ℤ))
    (hz : allocatedGridJetDensity B U b hR hσ S x u v rows
      (fun a => coefficientJetAxisEquiv jets I n z a.val) ≠ 0)
    (hsites : ∀ s a, |allocatedIdealSiteCoordinates B U b S (split z).2 s a| ≤ 2 * idealSiteBoxRadius α m) :
    ∀ s a, |allocatedFullMixedSiteValue (R := R) U b (mixedBooleanSiteValue z s) a| ≤
      allocatedFullSiteRadius (G := G) B α := by
  intro s a
  rcases a with ⟨j, i | i⟩
  · apply le_trans _ (allocatedFullSiteRadius_dominates (G := G) B α j)
    change |(mixedBooleanSiteValue z s j).1 i / R j| ≤ _
    rw [mixedBooleanSiteValue_real, ← realBoundedSiteReconstruction_div]
    apply realBoundedSiteReconstruction_bound _ _ (allocatedSiteJetSize_nonneg B α j)
    intro t
    rw [abs_div, abs_of_pos (hR j)]
    exact (div_le_iff₀ (hR j)).mpr
      ((allocatedSiteBox_mixed_coordinate_bounds B U b hR hσ S x u v hσ1 z hz hsites j t).1 i)
  · apply le_trans _ (allocatedFullSiteRadius_dominates (G := G) B α j)
    change |((mixedBooleanSiteValue z s j).2 i : ℝ) / basisAxisScale (b j) i / R j| ≤ _
    rw [mixedBooleanSiteValue_integer, ← realBoundedSiteReconstruction_div,
      ← realBoundedSiteReconstruction_div]
    apply realBoundedSiteReconstruction_bound _ _ (allocatedSiteJetSize_nonneg B α j)
    intro t
    rw [abs_div, abs_of_pos (hR j)]
    exact (div_le_iff₀ (hR j)).mpr
      ((allocatedSiteBox_mixed_coordinate_bounds B U b hR hσ S x u v hσ1 z hz hsites j t).2 i)

end Erdos3.VectorPolynomial

end

end OAI
