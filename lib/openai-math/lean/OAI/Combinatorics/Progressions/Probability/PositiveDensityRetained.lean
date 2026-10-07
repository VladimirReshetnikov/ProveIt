import OAI.Combinatorics.Progressions.Dynamics.VectorSiteBudget
import OAI.Combinatorics.Progressions.Geometry.PrincipalSpatialSiteComparison
import OAI.Combinatorics.Progressions.Geometry.SupportedMeanBounds

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem weightedFiber_complex_functional {X R V : Type*} [Fintype X] [Fintype R]
    (p : FiniteProbabilityWeights X) (F : X → R) (t : Finset V)
    (D : X → V → ℝ) (b : R → V → ℂ) (φ : V → ℂ) :
    p.complexMean (fun x => 𝔼 v ∈ t, (D x v : ℂ) * b (F x) v * φ v) =
      ∑ a, 𝔼 v ∈ t, (p.fiberMean F a (fun x => D x v) : ℂ) * b a v * φ v := by
  rw [p.complexMean_finset_expect, ← Finset.expect_sum_comm]
  apply Finset.expect_congr rfl
  intro v _
  simpa only [mul_assoc] using p.complexMean_fiber_factor F (fun x => D x v) (fun a => b a v * φ v)

theorem weightedFiber_complex_mixture {X R V : Type*} [Fintype X] [Fintype R]
    (p : FiniteProbabilityWeights X) (F : X → R) (t : Finset V)
    (D : X → V → ℝ) (a : X → V → ℂ) (b : R → V → ℂ) (φ : V → ℂ) {ε : ℝ}
    (hD : ∀ x, p.weight x ≠ 0 → ∀ v ∈ t, 0 ≤ D x v)
    (hφ : ∀ v ∈ t, ‖φ v‖ ≤ 1)
    (he : ∀ x, p.weight x ≠ 0 → ∀ v ∈ t, ‖a x v - b (F x) v‖ ≤ ε) :
    ‖p.complexMean (fun x => 𝔼 v ∈ t, (D x v : ℂ) * a x v * φ v) -
      ∑ r, 𝔼 v ∈ t, (p.fiberMean F r (fun x => D x v) : ℂ) * b r v * φ v‖ ≤
      ε * p.mean (fun x => 𝔼 v ∈ t, D x v) := by
  rw [← weightedFiber_complex_functional]
  apply (p.norm_complexMean_sub_le _ _ (fun x => ε * (𝔼 v ∈ t, D x v)) ?_).trans_eq
    (p.mean_const_mul ε _)
  intro x hx
  exact norm_weighted_complex_mean_sub_le t (D x) (a x) (b (F x)) φ (hD x hx) hφ (he x hx)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem norm_density_complex_factor_expect_sub_le {V : Type*} (t : Finset V)
    (a c : V → ℝ) (b φ : V → ℂ) {ε : ℝ}
    (hφ : ∀ v ∈ t, ‖φ v‖ ≤ 1) (he : ∀ v ∈ t, |a v-c v| ≤ ε) :
    ‖(𝔼 v ∈ t, (a v : ℂ)*b v*φ v) - (𝔼 v ∈ t, (c v : ℂ)*b v*φ v)‖ ≤
      ε*(𝔼 v ∈ t, ‖b v‖) := by
  rw [← Finset.expect_sub_distrib]
  apply (RCLike.norm_expect_le (K := ℂ)).trans
  calc
    _ ≤ 𝔼 v ∈ t, ε*‖b v‖ := by
      apply Finset.expect_le_expect
      intro v hv
      have hid : (a v : ℂ)*b v*φ v-(c v : ℂ)*b v*φ v =
          ((a v-c v : ℝ) : ℂ)*b v*φ v := by push_cast; ring
      rw [hid, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc
        _ ≤ |a v-c v| * ‖b v‖ * 1 := mul_le_mul_of_nonneg_left (hφ v hv) (by positivity)
        _ ≤ ε*‖b v‖ := by rw [mul_one]; exact mul_le_mul_of_nonneg_right (he v hv) (norm_nonneg _)
    _ = _ := (Finset.mul_expect _ _ _).symm

theorem fiberDensity_site_error {X R V : Type*} [Fintype X] [Fintype R]
    (p : FiniteProbabilityWeights X) (F : X → R) (t : Finset V)
    (c : X → V → ℝ) (target : R → V → ℝ) (b : R → V → ℂ) (φ : V → ℂ) {ε : ℝ}
    (hφ : ∀ v ∈ t, ‖φ v‖ ≤ 1)
    (he : ∀ r v, v ∈ t → |p.fiberMean F r (fun x => c x v)-(p.fiberLaw F).weight r*target r v| ≤
      (p.fiberLaw F).weight r*ε) :
    ‖(∑ r, 𝔼 v ∈ t, (p.fiberMean F r (fun x => c x v) : ℂ)*b r v*φ v) -
      (∑ r, 𝔼 v ∈ t, (((p.fiberLaw F).weight r*target r v : ℝ) : ℂ)*b r v*φ v)‖ ≤
        ε*(p.fiberLaw F).mean (fun r => 𝔼 v ∈ t, ‖b r v‖) := by
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ r, ((p.fiberLaw F).weight r*ε)*(𝔼 v ∈ t, ‖b r v‖) :=
      Finset.sum_le_sum (fun r _ => norm_density_complex_factor_expect_sub_le t _ _ _ φ hφ (he r))
    _ = _ := by
      unfold FiniteProbabilityWeights.mean
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      ring

theorem mixed_residue_comparison {X R V : Type*} [Fintype X] [Fintype R]
    (p : FiniteProbabilityWeights X) (F : X → R) (t : Finset V)
    (c : X → V → ℝ) (target : R → V → ℝ)
    (a : X → V → ℂ) (b : R → V → ℂ) (φ : V → ℂ) {δ ε : ℝ}
    (hc : ∀ x, p.weight x ≠ 0 → ∀ v ∈ t, 0 ≤ c x v)
    (hφ : ∀ v ∈ t, ‖φ v‖ ≤ 1)
    (hspatial : ∀ x, p.weight x ≠ 0 → ∀ v ∈ t, ‖a x v-b (F x) v‖ ≤ δ)
    (hcoeff : ∀ r v, v ∈ t → |p.fiberMean F r (fun x => c x v)-(p.fiberLaw F).weight r*target r v| ≤
      (p.fiberLaw F).weight r*ε) :
    ‖p.complexMean (fun x => 𝔼 v ∈ t, (c x v : ℂ)*a x v*φ v) -
      (∑ r, 𝔼 v ∈ t, (((p.fiberLaw F).weight r*target r v : ℝ) : ℂ)*b r v*φ v)‖ ≤
        δ*p.mean (fun x => 𝔼 v ∈ t, c x v) +
          ε*(p.fiberLaw F).mean (fun r => 𝔼 v ∈ t, ‖b r v‖) := by
  have h₁ := weightedFiber_complex_mixture p F t c a b φ hc hφ hspatial
  have h₂ := fiberDensity_site_error p F t c target b φ hφ hcoeff
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add h₁ h₂)

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {X R : Type*} [Fintype X] [DecidableEq X] [Fintype R] [DecidableEq R]

theorem fiberLaw_weight_eq_mass (p : FiniteProbabilityWeights X) (F : X → R) (r : R) :
    (p.fiberLaw F).weight r = p.mass (Finset.univ.filter (fun x => F x = r)) := by
  simpa only [fiberLaw_weight, fiberMean, Finset.mem_filter, Finset.mem_univ, true_and]
    using p.mean_indicator (Finset.univ.filter (fun x => F x = r))

theorem fiberMean_zero (p : FiniteProbabilityWeights X) (F : X → R) (r : R)
    (hr : (p.fiberLaw F).weight r = 0) (f : X → ℝ) : p.fiberMean F r f = 0 := by
  rw [fiberLaw_weight_eq_mass] at hr
  calc
    _ = p.mean (fun x => if x ∈ Finset.univ.filter (fun x => F x = r) then f x else 0) := by
      unfold fiberMean
      congr 1
      funext x
      by_cases hx : F x = r <;> simp [hx]
    _ = 0 := p.mean_mask_zero _ hr f

theorem fiberMean_condition_error (p : FiniteProbabilityWeights X) (F : X → R) (r : R)
    (f : X → ℝ) {target ε : ℝ}
    (he : ∀ hr : 0 < p.mass (Finset.univ.filter (fun x => F x = r)),
      |(p.condition _ hr).mean f-target| ≤ ε) :
    |p.fiberMean F r f-(p.fiberLaw F).weight r*target| ≤ (p.fiberLaw F).weight r*ε := by
  by_cases hr : 0 < p.mass (Finset.univ.filter (fun x => F x = r))
  · rw [fiberMean_eq_mass_mul_condition p F r f hr, fiberLaw_weight_eq_mass,
      ← mul_sub, abs_mul, abs_of_nonneg (p.mass_nonneg _)]
    exact mul_le_mul_of_nonneg_left (he hr) (p.mass_nonneg _)
  · have hz : (p.fiberLaw F).weight r = 0 := by
      rw [fiberLaw_weight_eq_mass]
      exact le_antisymm (le_of_not_gt hr) (p.mass_nonneg _)
    rw [fiberMean_zero p F r hz f, hz]
    simp

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators

theorem frozen_mixed_residue_comparison {Z : Type*} [Fintype Z]
    {X R V : Z → Type*} [∀ z, Fintype (X z)] [∀ z, Fintype (R z)]
    (outer : FiniteProbabilityWeights Z) (p : ∀ z, FiniteProbabilityWeights (X z))
    (label : ∀ z, X z → R z) (t : ∀ z, Finset (V z))
    (c : ∀ z, X z → V z → ℝ) (target : ∀ z, R z → V z → ℝ)
    (a : ∀ z, X z → V z → ℂ) (b : ∀ z, R z → V z → ℂ) (φ : ∀ z, V z → ℂ)
    {δ ε : ℝ}
    (hc : ∀ z, outer.weight z ≠ 0 → ∀ x, (p z).weight x ≠ 0 → ∀ v ∈ t z, 0 ≤ c z x v)
    (hφ : ∀ z, outer.weight z ≠ 0 → ∀ v ∈ t z, ‖φ z v‖ ≤ 1)
    (hspatial : ∀ z, outer.weight z ≠ 0 → ∀ x, (p z).weight x ≠ 0 →
      ∀ v ∈ t z, ‖a z x v-b z (label z x) v‖ ≤ δ)
    (hcoeff : ∀ z, outer.weight z ≠ 0 → ∀ r v, v ∈ t z →
      |(p z).fiberMean (label z) r (fun x => c z x v)-((p z).fiberLaw (label z)).weight r*target z r v| ≤
        ((p z).fiberLaw (label z)).weight r*ε) :
    ‖outer.complexMean (fun z => (p z).complexMean
        (fun x => 𝔼 v ∈ t z, (c z x v : ℂ)*a z x v*φ z v)) -
      outer.complexMean (fun z => ∑ r, 𝔼 v ∈ t z,
        ((((p z).fiberLaw (label z)).weight r*target z r v : ℝ) : ℂ)*b z r v*φ z v)‖ ≤
      δ*outer.mean (fun z => (p z).mean (fun x => 𝔼 v ∈ t z, c z x v)) +
        ε*outer.mean (fun z => ((p z).fiberLaw (label z)).mean (fun r => 𝔼 v ∈ t z, ‖b z r v‖)) := by
  calc
    _ ≤ outer.mean (fun z => δ*(p z).mean (fun x => 𝔼 v ∈ t z, c z x v) +
        ε*((p z).fiberLaw (label z)).mean (fun r => 𝔼 v ∈ t z, ‖b z r v‖)) :=
      outer.norm_complexMean_sub_le _ _ _ (fun z hz => mixed_residue_comparison
        (p z) (label z) (t z) (c z) (target z) (a z) (b z) (φ z)
        (hc z hz) (hφ z hz) (hspatial z hz) (hcoeff z hz))
    _ = _ := by rw [outer.mean_add, outer.mean_const_mul, outer.mean_const_mul]

theorem frozen_mixed_residue_comparison_of_mass {Z : Type*} [Fintype Z]
    {X R V : Z → Type*} [∀ z, Fintype (X z)] [∀ z, Fintype (R z)]
    (outer : FiniteProbabilityWeights Z) (p : ∀ z, FiniteProbabilityWeights (X z))
    (label : ∀ z, X z → R z) (t : ∀ z, Finset (V z))
    (c : ∀ z, X z → V z → ℝ) (target : ∀ z, R z → V z → ℝ)
    (a : ∀ z, X z → V z → ℂ) (b : ∀ z, R z → V z → ℂ) (φ : ∀ z, V z → ℂ)
    {δ ε C S : ℝ} (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hc : ∀ z, outer.weight z ≠ 0 → ∀ x, (p z).weight x ≠ 0 → ∀ v ∈ t z, 0 ≤ c z x v)
    (hφ : ∀ z, outer.weight z ≠ 0 → ∀ v ∈ t z, ‖φ z v‖ ≤ 1)
    (hspatial : ∀ z, outer.weight z ≠ 0 → ∀ x, (p z).weight x ≠ 0 →
      ∀ v ∈ t z, ‖a z x v-b z (label z x) v‖ ≤ δ)
    (hcoeff : ∀ z, outer.weight z ≠ 0 → ∀ r v, v ∈ t z →
      |(p z).fiberMean (label z) r (fun x => c z x v)-((p z).fiberLaw (label z)).weight r*target z r v| ≤
        ((p z).fiberLaw (label z)).weight r*ε)
    (hC : ∀ z, outer.weight z ≠ 0 → (p z).mean (fun x => 𝔼 v ∈ t z, c z x v) ≤ C)
    (hS : ∀ z, outer.weight z ≠ 0 →
      ((p z).fiberLaw (label z)).mean (fun r => 𝔼 v ∈ t z, ‖b z r v‖) ≤ S) :
    ‖outer.complexMean (fun z => (p z).complexMean
        (fun x => 𝔼 v ∈ t z, (c z x v : ℂ)*a z x v*φ z v)) -
      outer.complexMean (fun z => ∑ r, 𝔼 v ∈ t z,
        ((((p z).fiberLaw (label z)).weight r*target z r v : ℝ) : ℂ)*b z r v*φ z v)‖ ≤ δ*C+ε*S := by
  apply (frozen_mixed_residue_comparison outer p label t c target a b φ hc hφ hspatial hcoeff).trans
  exact add_le_add
    (mul_le_mul_of_nonneg_left (finiteMean_le_of_support outer _ hC) hδ)
    (mul_le_mul_of_nonneg_left (finiteMean_le_of_support outer _ hS) hε)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem smoothVectorSpatial_site_mixture {D I J N X : Type*}
    [Fintype D] [DecidableEq D] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype N] [DecidableEq N] [Fintype X]
    {L B : ℕ} {ρ ξ ε : ℝ} (s : I ↪ J) (x : J → IntegerScalarCubeBox I L) (root : J → ℤ)
    (hB : 0 < B) (hL : 0 < L) (hx : GoodScalarKernelTuple s (1 / (B : ℝ)) B x)
    (hroot : ∀ j, |root j| ≤ (L : ℤ)) (m : ℕ) [NeZero m]
    (hp : integerScalarLattice (Unit ⊕ I) (m : ℤ) ≤
      pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) s)
        (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) s))
    (p : FiniteProbabilityWeights X) (C : X → D → Matrix (Unit ⊕ I) N ℤ)
    (H : D → ℝ) (Q : D → N → ℝ) (hH : ∀ d, 0 < H d) (hQ : ∀ d j, 0 < Q d j)
    (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (hC : ∀ y, p.weight y ≠ 0 → ∀ d i j, |(C y d i j : ℝ)| * Q d j ≤ ξ * H d)
    (hρ : 0 < ρ) (hscale : ∀ d, ρ ≤ H d / L) (hscaleQ : ∀ d j, ρ ≤ Q d j)
    (hlarge : smoothSpatialMeshThreshold I J N L ≤ ρ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hsmall : smoothSpatialError N s B L ρ ξ ≤ vectorSpatialAccuracy (Fintype.card D)
      (2 + (m : ℝ)^Fintype.card (Unit ⊕ I) * smoothSpatialDensityCap s B) ε)
    (t : Finset (D → (Unit ⊕ I) → ℤ)) (W : X → (D → (Unit ⊕ I) → ℤ) → ℝ)
    (φ : (D → (Unit ⊕ I) → ℤ) → ℂ)
    (hW : ∀ y, p.weight y ≠ 0 → ∀ v ∈ t, 0 ≤ W y v)
    (hφ : ∀ v ∈ t, ‖φ v‖ ≤ 1)
    (ht : ∀ v ∈ t, ∀ d i, |((spatialStar (v d) i : ℤ) : ℝ) / H d| ≤ 1) :
    let A := selectedSpatialPivot root (scalarCubeDifferenceMatrix x) s
    let A' := selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) s
    let hA := goodScalarKernelTuple_spatial_det_ne_zero s x root
      (one_div_pos.mpr (by exact_mod_cast hB)) hx
    let f := fun d => smoothSpatialKernelDensity s root (scalarCubeDifferenceMatrix x) hA
      (H d) L (hH d) (by exact_mod_cast hL)
    let G := (m : ℝ)^Fintype.card (Unit ⊕ I)
    let δ := vectorSpatialAccuracy (Fintype.card D) (2 + G*smoothSpatialDensityCap s B) ε
    let r := spatialSiteRadius G (smoothSpatialDensityLip s B) δ
    ‖p.complexMean (fun y => 𝔼 v ∈ t, (W y v : ℂ) *
        (((∏ d, ∏ _i : Unit ⊕ I, H d) *
          (smoothVectorSpatialOutputLaw root (scalarCubeDifferenceMatrix x) (C y) H L Q hH
            (by exact_mod_cast hL) hQ v).toReal : ℝ) : ℂ) * φ v) -
      ∑ a : D → Matrix (Unit ⊕ I) N (ZMod m), 𝔼 v ∈ t,
        (p.fiberMean (fun y d => integerResidueMatrix (C y d) m) a (fun y => W y v) : ℂ) *
          (∏ d, spatialSiteApprox A (Matrix.fromCols A' (liftResidueMatrix (a d)))
            m (f d) (H d) 1 r (v d)) * φ v‖ ≤
      ε * p.mean (fun y => 𝔼 v ∈ t, W y v) := by
  dsimp only
  have hG : 0 ≤ (m : ℝ)^Fintype.card (Unit ⊕ I) := by positivity
  have hcap := smoothSpatialDensityCap_nonneg s B
  have hK := smoothSpatialDensityLip_nonneg s B
  have hδ := vectorSpatialAccuracy_pos (Fintype.card D)
    (show 0 < 2 + (m : ℝ)^Fintype.card (Unit ⊕ I) * smoothSpatialDensityCap s B by positivity) hε
  have hr := spatialSiteRadius_pos hG hK hδ
  apply weightedFiber_complex_mixture p _ t W _ _ φ hW hφ
  intro y hy v hv
  have h := smoothVectorSpatial_site_error s x root hB hL hx hroot m hp (C y) H Q hH hQ
    hξ0 hξ1 (hC y hy) hρ hscale hscaleQ hlarge hr v (ht v hv)
  exact h.trans (vectorSpatialSiteError_le (Fintype.card D) hG hcap hK
    (smoothSpatialError_nonneg N s B L hρ.le hξ0) hε hε1 hsmall)

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

theorem reweightPositive_retained_fiber_mass_pos {X R : Type*}
    [Fintype X] [DecidableEq X] [Fintype R] [DecidableEq R]
    (p : FiniteProbabilityWeights X) (F : X → R) (w : X → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hm : 0 < p.mean w) {η : ℝ} (hη : 0 < η) (r : R)
    (hr : r ∉ p.lowWeightFibers F w η)
    (hbase : 0 < p.mass (Finset.univ.filter (fun x => F x = r))) :
    0 < (p.reweightPositive w hw hm).mass (Finset.univ.filter (fun x => F x = r)) := by
  have hb : 0 < (p.fiberLaw F).weight r := by
    rw [p.fiberLaw_weight_eq_mass]
    exact hbase
  have hmean := p.retained_fiber_weight_mean_ge F w η r hr hb
  have hnum : 0 < p.fiberMean F r w :=
    (mul_pos hη hb).trans_le ((le_div_iff₀ hb).mp hmean)
  rw [← fiberLaw_weight_eq_mass, reweightPositive_fiberLaw_weight]
  exact div_pos hnum hm

end Erdos3.FiniteProbabilityWeights

end

end OAI
