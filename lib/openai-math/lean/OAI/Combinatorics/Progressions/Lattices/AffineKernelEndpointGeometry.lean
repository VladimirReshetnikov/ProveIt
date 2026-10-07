import OAI.Combinatorics.Progressions.Estimates.DenseProgressionInnerFamily
import OAI.Combinatorics.Progressions.Estimates.JointCoefficientRetainedTest

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {J I : Type*} [Fintype J] [Fintype I]

def affineCubeTuple (lower width : J → ℝ) (x : J → Option I → ℝ) : J → Option I → ℝ :=
  fun j i => (if i = none then lower j else 0) + width j * x j i

theorem affineCubeTuple_lipschitz (lower width : J → ℝ) (K : ℝ≥0)
    (hw : ∀ j, |width j| ≤ K) : LipschitzWith K (affineCubeTuple (I := I) lower width) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  apply (dist_pi_le_iff (mul_nonneg K.coe_nonneg dist_nonneg)).mpr
  intro j
  apply (dist_pi_le_iff (mul_nonneg K.coe_nonneg dist_nonneg)).mpr
  intro i
  simp only [affineCubeTuple, dist_add_left, Real.dist_eq, ← mul_sub, abs_mul]
  simpa only [Real.dist_eq] using mul_le_mul (hw j)
    ((dist_le_pi_dist (x j) (y j) i).trans (dist_le_pi_dist x y j))
    dist_nonneg K.coe_nonneg

theorem affineCubeTuple_width_dist (lower w v : J → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hw : ∀ j, |w j - v j| ≤ ε) (x : J → Option I → ℝ) (hx : ‖x‖ ≤ 1) :
    dist (affineCubeTuple lower w x) (affineCubeTuple lower v x) ≤ ε := by
  apply (dist_pi_le_iff hε).mpr
  intro j
  apply (dist_pi_le_iff hε).mpr
  intro i
  have hxj : |x j i| ≤ 1 := by
    exact (norm_le_pi_norm (x j) i).trans ((norm_le_pi_norm x j).trans hx)
  simp only [affineCubeTuple, dist_add_left, Real.dist_eq, ← sub_mul, abs_mul]
  exact (mul_le_mul (hw j) hxj (abs_nonneg _) hε).trans_eq (mul_one _)

theorem affineCubeTuple_integral_width_error [DecidableEq I]
    (lower w v : J → ℝ) {ε : ℝ} (hε : 0 ≤ ε) (hw : ∀ j, |w j - v j| ≤ ε)
    (φ : (J → Option I → ℝ) → ℝ) {K : ℝ≥0} {A : ℝ}
    (hφ : LipschitzWith K φ) (_hA : 0 ≤ A) (hb : ∀ x, ‖φ x‖ ≤ A) :
    |(∫ x, φ (affineCubeTuple lower w x) ∂scalarCubeProductMeasure J I) -
      ∫ x, φ (affineCubeTuple lower v x) ∂scalarCubeProductMeasure J I| ≤ K * ε := by
  have hm (v : J → ℝ) : Measurable (affineCubeTuple (I := I) lower v) := by
    unfold affineCubeTuple
    fun_prop
  have hi (v : J → ℝ) : Integrable (fun x => φ (affineCubeTuple lower v x)) (scalarCubeProductMeasure J I) :=
    Integrable.mono' (integrable_const A) (hφ.continuous.measurable.comp (hm v)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => hb _))
  rw [← integral_sub (hi w) (hi v)]
  have he : ∀ᵐ x ∂scalarCubeProductMeasure J I,
      ‖φ (affineCubeTuple lower w x) - φ (affineCubeTuple lower v x)‖ ≤ K * ε := by
    filter_upwards [scalarCubeProductMeasure_ae_closedBall J I] with x hx
    rw [Metric.mem_closedBall, dist_zero_right] at hx
    rw [← dist_eq_norm]
    exact (hφ.dist_le_mul _ _).trans
      (mul_le_mul_of_nonneg_left (affineCubeTuple_width_dist lower w v hε hw x hx) K.coe_nonneg)
  have ht := norm_integral_le_of_norm_le (integrable_const ((K : ℝ) * ε) (μ := scalarCubeProductMeasure J I)) he
  simpa only [Real.norm_eq_abs, integral_const, probReal_univ, one_smul] using ht

theorem affineCubeTuple_residue_riemann [DecidableEq J] [DecidableEq I]
    (H M : J → ℕ) (hH : ∀ j, 0 < H j) (modulus : J → Option I → ℕ)
    (residue : ∀ j i, ZMod (modulus j i))
    (hm : ∀ j i, 0 < modulus j i) (hmM : ∀ j i, modulus j i ≤ M j)
    (hsize : ∀ j, (Fintype.card I + 1) * M j ≤ H j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant I * ((M j : ℝ) / H j) < volume.real (scalarCubeDomain I))
    (lower w v : J → ℝ) (W : ℝ≥0) (hw : ∀ j, |w j| ≤ W)
    {ε : ℝ} (hε : 0 ≤ ε) (hwidth : ∀ j, |w j - v j| ≤ ε)
    (φ : (J → Option I → ℝ) → ℝ) {K : ℝ≥0} {A : ℝ}
    (hφ : LipschitzWith K φ) (hA : 0 ≤ A) (hb : ∀ x, ‖φ x‖ ≤ A) :
    |(FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights I (H j) (M j) (hH j)
      (modulus j) (residue j) (hm j) (hmM j) (hsize j))).mean
        (fun z => φ (affineCubeTuple lower w (fun j i => (z j i : ℝ) / H j))) -
      ∫ x, φ (affineCubeTuple lower v x) ∂scalarCubeProductMeasure J I| ≤
      (2 * A * scalarCubeGridBoundaryConstant I / volume.real (scalarCubeDomain I) + K * W) *
        ∑ j, (M j : ℝ) / H j + K * ε := by
  have htest := hφ.comp (affineCubeTuple_lipschitz lower w W hw)
  have he := scalarCubeResidueWeights_pi_riemann H M hH modulus residue hm hmM hsize hsmall
    (φ ∘ affineCubeTuple lower w) htest hA (fun x => hb _)
  have hi := affineCubeTuple_integral_width_error lower w v hε hwidth φ hφ hA hb
  exact (abs_sub_le _ _ _).trans (add_le_add he hi)

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators NNReal Classical
variable {G : Type*} [Fintype G]

noncomputable def affineKernelContinuousPoint (lower : G → ℝ) (step S : ℝ) (H : G → ℕ)
    (x : G → Option Empty → ℝ) : G → ℝ :=
  fun g => (lower g + step * ((H g - 1 : ℕ) : ℝ) * x g none) / S

noncomputable def affineKernelDiscretePoint (lower : G → ℝ) (step S : ℝ) {H : G → ℕ}
    (z : ∀ g, IntegerScalarCubeBox Empty (H g)) : G → ℝ :=
  fun g => (lower g + step * (z g none : ℝ)) / S

theorem affineKernelContinuousPoint_lipschitz (lower : G → ℝ) (step S : ℝ) (H : G → ℕ)
    (hS : 0 < S) (hstep : 0 ≤ step)
    (hspan : ∀ g, step * ((H g - 1 : ℕ) : ℝ) ≤ S) :
    LipschitzWith 1 (affineKernelContinuousPoint lower step S H) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul]
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro g
  have hw0 : 0 ≤ step * ((H g - 1 : ℕ) : ℝ) := mul_nonneg hstep (Nat.cast_nonneg _)
  have hw : step * ((H g - 1 : ℕ) : ℝ) / S ≤ 1 := (div_le_one hS).mpr (hspan g)
  have hx : |x g none - y g none| ≤ dist x y :=
    (dist_le_pi_dist (x g) (y g) none).trans (dist_le_pi_dist x y g)
  change |(lower g + step * ((H g - 1 : ℕ) : ℝ) * x g none) / S -
      (lower g + step * ((H g - 1 : ℕ) : ℝ) * y g none) / S| ≤ _
  rw [← sub_div, add_sub_add_left_eq_sub, ← mul_sub, abs_div, abs_mul,
    abs_of_nonneg hw0, abs_of_pos hS]
  calc
    _ = (step * ((H g - 1 : ℕ) : ℝ) / S) * |x g none - y g none| := by ring
    _ ≤ 1 * dist x y := mul_le_mul hw hx (abs_nonneg _) zero_le_one
    _ = _ := one_mul _

theorem affineKernelEndpoint_dist_le (lower : G → ℝ) (step S : ℝ) (H : G → ℕ)
    (hH : ∀ g, 0 < H g) (hS : 0 < S) (hstep : 0 ≤ step)
    (hspan : ∀ g, step * ((H g - 1 : ℕ) : ℝ) ≤ S)
    (z : ∀ g, IntegerScalarCubeBox Empty (H g))
    (hz : (FiniteProbabilityWeights.pi
      (fun g => integerScalarCubeWeights Empty (H g) (hH g))).weight z ≠ 0) :
    dist (affineKernelDiscretePoint lower step S z)
      (affineKernelContinuousPoint lower step S H (fun g i => (z g i : ℝ) / H g)) ≤
        ∑ g, (1 : ℝ) / H g := by
  have hsum : 0 ≤ ∑ g, (1 : ℝ) / H g := Finset.sum_nonneg (fun g _ => by positivity)
  apply (dist_pi_le_iff hsum).mpr
  intro g
  have hz' := integerScalarCubePi_root_real_bounds H hH z hz g
  have he := affineKernelEndpoint_error_nat (lower g) (hH g) hS hz'.1 hz'.2 hstep (hspan g)
  change |(lower g + step * (z g none : ℝ)) / S -
    (lower g + step * ((H g - 1 : ℕ) : ℝ) * ((z g none : ℝ) / H g)) / S| ≤ _
  exact he.trans (Finset.single_le_sum (f := fun j => (1 : ℝ) / H j)
    (fun j _ => by positivity) (Finset.mem_univ g))

end Erdos3

end

end OAI
