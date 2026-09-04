import FabiusFunction.LambertWBranchPointGeometry
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Calculus.LHopital

/-!
# Leading asymptotics at the real Lambert branch point

The two real Lambert branches meet at `-exp (-1)` with value `-1`.  Their
common intrinsic branch-point scale is

`sqrt (2 * exp 1 * (z + exp (-1)))`.

This module proves the signed first-order laws

`W₀(z) + 1 ~  sqrt (2 * exp 1 * (z + exp (-1)))`,

`W₋₁(z) + 1 ~ -sqrt (2 * exp 1 * (z + exp (-1)))`

as `z` approaches the branch point from the right.  The proof first applies
one-sided L'Hôpital asymptotics to the forward map `w ↦ w * exp w`, whose
first nonzero term at `w = -1` is quadratic.  Exact branch equations then
transport that quadratic ratio to both inverse branches, and positivity of
the appropriate signed displacement selects the correct square root.

The square-root step is the branch-free lemma `isEquivalent_sqrt_of_sq`
(`u ^ 2 ~ v` with `u`, `v` eventually nonnegative gives `u ~ √v`).

Only the leading square-root law is asserted here.  In particular, no
higher Puiseux coefficient or remainder estimate is claimed.
-/

set_option autoImplicit false

open Set Filter Asymptotics
open scoped Filter Topology

namespace Fabius

noncomputable section

/-! ## The intrinsic scale -/

/-- The intrinsic positive square-root scale at the real Lambert branch
point.  On the natural right-hand domain its radicand is strictly positive. -/
noncomputable def lambertWBranchPointScale (z : ℝ) : ℝ :=
  Real.sqrt (2 * Real.exp 1 * (z + Real.exp (-1)))

/-- The intrinsic branch-point scale is positive strictly to the right of
the branch point. -/
theorem lambertWBranchPointScale_pos {z : ℝ}
    (hz : -Real.exp (-1) < z) :
    0 < lambertWBranchPointScale z := by
  rw [lambertWBranchPointScale, Real.sqrt_pos]
  exact mul_pos (mul_pos (by norm_num) (Real.exp_pos 1)) (by linarith)

/-- Squaring the intrinsic scale recovers the normalized displacement from
the branch point. -/
theorem lambertWBranchPointScale_sq {z : ℝ}
    (hz : -Real.exp (-1) < z) :
    lambertWBranchPointScale z ^ 2 =
      2 * Real.exp 1 * (z + Real.exp (-1)) := by
  rw [lambertWBranchPointScale, Real.sq_sqrt]
  exact (mul_pos (mul_pos (by norm_num) (Real.exp_pos 1))
    (by linarith)).le

/-! ## Quadratic asymptotics of the forward map -/

private theorem tendsto_mul_exp_branchPoint_quadraticRatio :
    Tendsto
      (fun w : ℝ ↦
        (w * Real.exp w + Real.exp (-1)) /
          ((w + 1) * (w + 1)))
      (𝓝[≠] (-1 : ℝ)) (𝓝 (Real.exp (-1) / 2)) := by
  have hne : ∀ᶠ w : ℝ in 𝓝[≠] (-1 : ℝ), w ≠ -1 := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    simpa using hw
  refine HasDerivAt.lhopital_zero_nhdsNE
    (f' := fun w : ℝ ↦ Real.exp w * (w + 1))
    (g' := fun w : ℝ ↦ 2 * (w + 1))
    ?_ ?_ ?_ ?_ ?_ ?_
  · filter_upwards with w
    have hraw :=
      ((hasDerivAt_id w).mul (Real.hasDerivAt_exp w)).add_const
        (Real.exp (-1))
    exact hraw.congr_deriv (by simp only [id_eq]; ring)
  · filter_upwards with w
    have hbase := (hasDerivAt_id w).add_const 1
    have hraw := hbase.mul hbase
    exact hraw.congr_deriv (by simp only [id_eq]; ring)
  · filter_upwards [hne] with w hw
    refine mul_ne_zero (by norm_num) ?_
    intro hw1
    apply hw
    linarith
  · have hcont :
        ContinuousAt
          (fun w : ℝ ↦ w * Real.exp w + Real.exp (-1)) (-1) :=
      (continuousAt_id.mul Real.continuous_exp.continuousAt).add continuousAt_const
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  · have hbase : ContinuousAt (fun w : ℝ ↦ w + 1) (-1) :=
      continuousAt_id.add continuousAt_const
    have hcont :
        ContinuousAt (fun w : ℝ ↦ (w + 1) * (w + 1)) (-1) :=
      hbase.mul hbase
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  · have hcont :
        ContinuousAt (fun w : ℝ ↦ Real.exp w / 2) (-1) :=
      Real.continuous_exp.continuousAt.div_const 2
    have hlim :
        Tendsto (fun w : ℝ ↦ Real.exp w / 2)
          (𝓝[≠] (-1 : ℝ)) (𝓝 (Real.exp (-1) / 2)) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    refine hlim.congr' ?_
    filter_upwards [hne] with w hw
    have hw1 : w + 1 ≠ 0 := by
      intro h
      apply hw
      linarith
    field_simp [hw1]

private lemma inv_exp_neg_one_div_two :
    (Real.exp (-1) / 2)⁻¹ = 2 * Real.exp 1 := by
  rw [inv_div, div_eq_mul_inv, ← Real.exp_neg]
  norm_num

private theorem tendsto_principalLambertW_branchPoint_nhdsNE :
    Tendsto principalLambertW
      (𝓝[>] (-Real.exp (-1))) (𝓝[≠] (-1 : ℝ)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · have hWclosed :
        Tendsto principalLambertW
          (𝓝[Set.Ici (-Real.exp (-1))] (-Real.exp (-1)))
          (𝓝 (-1 : ℝ)) := by
      simpa only [principalLambertW_branchPoint] using
        principalLambertW_continuousWithinAt_branchPoint.tendsto
    exact hWclosed.mono_left
      (nhdsWithin_mono _ Ioi_subset_Ici_self)
  · filter_upwards [self_mem_nhdsWithin] with z hz
    simpa using (ne_of_gt (neg_one_lt_principalLambertW hz))

private theorem tendsto_lowerLambertW_branchPoint_nhdsNE :
    Tendsto lowerLambertW
      (𝓝[>] (-Real.exp (-1))) (𝓝[≠] (-1 : ℝ)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · have hWclosed :
        Tendsto lowerLambertW
          (𝓝[Set.Ico (-Real.exp (-1)) 0] (-Real.exp (-1)))
          (𝓝 (-1 : ℝ)) := by
      simpa only [lowerLambertW_branchPoint] using
        lowerLambertW_continuousWithinAt_branchPoint.tendsto
    exact hWclosed.mono_left nhdsGT_branchPoint_le_nhdsWithin_Ico
  · filter_upwards [Ioo_mem_nhdsGT_branchPoint] with z hz
    simpa using (ne_of_lt (lowerLambertW_lt_neg_one hz))

/-! ## Exact squared ratios -/

/-- The squared principal-branch displacement divided by the input
displacement tends to `2 * exp 1`. -/
theorem tendsto_principalLambertW_add_one_sq_div_branchPoint :
    Tendsto
      (fun z : ℝ ↦
        (principalLambertW z + 1) ^ 2 /
          (z + Real.exp (-1)))
      (𝓝[>] (-Real.exp (-1))) (𝓝 (2 * Real.exp 1)) := by
  have hforward := tendsto_mul_exp_branchPoint_quadraticRatio.comp
    tendsto_principalLambertW_branchPoint_nhdsNE
  have hratio :
      Tendsto
        (fun z : ℝ ↦
          (z + Real.exp (-1)) /
            ((principalLambertW z + 1) *
              (principalLambertW z + 1)))
        (𝓝[>] (-Real.exp (-1))) (𝓝 (Real.exp (-1) / 2)) := by
    refine hforward.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    simp only [Function.comp_apply]
    rw [principalLambertW_mul_exp hz.le]
  have hinv := hratio.inv₀ (by positivity : Real.exp (-1) / 2 ≠ 0)
  rw [inv_exp_neg_one_div_two] at hinv
  simpa only [Pi.inv_apply, inv_div, pow_two] using hinv

/-- The squared lower-branch displacement divided by the input displacement
has the same limit `2 * exp 1`. -/
theorem tendsto_lowerLambertW_add_one_sq_div_branchPoint :
    Tendsto
      (fun z : ℝ ↦
        (lowerLambertW z + 1) ^ 2 /
          (z + Real.exp (-1)))
      (𝓝[>] (-Real.exp (-1))) (𝓝 (2 * Real.exp 1)) := by
  have hforward := tendsto_mul_exp_branchPoint_quadraticRatio.comp
    tendsto_lowerLambertW_branchPoint_nhdsNE
  have hratio :
      Tendsto
        (fun z : ℝ ↦
          (z + Real.exp (-1)) /
            ((lowerLambertW z + 1) * (lowerLambertW z + 1)))
        (𝓝[>] (-Real.exp (-1))) (𝓝 (Real.exp (-1) / 2)) := by
    refine hforward.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT_branchPoint] with z hz
    simp only [Function.comp_apply]
    rw [lowerLambertW_mul_exp hz]
  have hinv := hratio.inv₀ (by positivity : Real.exp (-1) / 2 ≠ 0)
  rw [inv_exp_neg_one_div_two] at hinv
  simpa only [Pi.inv_apply, inv_div, pow_two] using hinv

/-! ## Squared and signed asymptotic equivalences -/

/-- The square of the principal-branch displacement is asymptotic to the
normalized input displacement. -/
theorem principalLambertW_add_one_sq_isEquivalent_branchPoint :
    (fun z : ℝ ↦ (principalLambertW z + 1) ^ 2)
      ~[𝓝[>] (-Real.exp (-1))]
        (fun z : ℝ ↦
          2 * Real.exp 1 * (z + Real.exp (-1))) := by
  apply isEquivalent_of_tendsto_one
  convert
    tendsto_principalLambertW_add_one_sq_div_branchPoint.div_const
      (2 * Real.exp 1) using 1
  · ext z
    simp only [Pi.div_apply, div_eq_mul_inv, mul_inv]
    ring
  · field_simp [Real.exp_ne_zero]

/-- The square of the lower-branch displacement has the same normalized
quadratic equivalent. -/
theorem lowerLambertW_add_one_sq_isEquivalent_branchPoint :
    (fun z : ℝ ↦ (lowerLambertW z + 1) ^ 2)
      ~[𝓝[>] (-Real.exp (-1))]
        (fun z : ℝ ↦
          2 * Real.exp 1 * (z + Real.exp (-1))) := by
  apply isEquivalent_of_tendsto_one
  convert
    tendsto_lowerLambertW_add_one_sq_div_branchPoint.div_const
      (2 * Real.exp 1) using 1
  · ext z
    simp only [Pi.div_apply, div_eq_mul_inv, mul_inv]
    ring
  · field_simp [Real.exp_ne_zero]

/-- **Square roots of asymptotic equivalences.**  If `u ^ 2 ~ v` along
`l`, with `u` and `v` eventually nonnegative, then `u ~ √v`.  The lemma
carries no Lambert content. -/
theorem isEquivalent_sqrt_of_sq
    {u v : ℝ → ℝ} {l : Filter ℝ}
    (hu : ∀ᶠ z in l, 0 ≤ u z)
    (hv : ∀ᶠ z in l, 0 ≤ v z)
    (hsq : (fun z : ℝ ↦ u z ^ 2) ~[l] v) :
    u ~[l] (fun z : ℝ ↦ Real.sqrt (v z)) := by
  have hvmax :
      v =ᶠ[l] (fun z : ℝ ↦ max 0 (v z)) := by
    filter_upwards [hv] with z hz
    exact (max_eq_right hz).symm
  have hsqMax :
      (fun z : ℝ ↦ u z ^ 2) ~[l]
        (fun z : ℝ ↦ max 0 (v z)) :=
    hsq.congr_right hvmax
  have hrpow :=
    IsEquivalent.rpow
      (r := (1 / 2 : ℝ))
      (fun z : ℝ ↦ le_max_left (0 : ℝ) (v z)) hsqMax
  change
    (fun z : ℝ ↦ (u z ^ 2) ^ (1 / 2 : ℝ)) ~[l]
      (fun z : ℝ ↦ (max 0 (v z)) ^ (1 / 2 : ℝ)) at hrpow
  have hsqrt :
      (fun z : ℝ ↦ Real.sqrt (u z ^ 2)) ~[l]
        (fun z : ℝ ↦ Real.sqrt (max 0 (v z))) := by
    simpa only [Real.sqrt_eq_rpow] using hrpow
  refine (hsqrt.congr_left ?_).congr_right ?_
  · filter_upwards [hu] with z hz
    rw [Real.sqrt_sq hz]
  · filter_upwards [hv] with z hz
    rw [max_eq_right hz]

/-- Leading principal-branch Puiseux law: the displacement above `-1` is
asymptotic to the intrinsic positive square-root scale. -/
theorem principalLambertW_add_one_isEquivalent_branchPoint :
    (fun z : ℝ ↦ principalLambertW z + 1)
      ~[𝓝[>] (-Real.exp (-1))] lambertWBranchPointScale := by
  have hu :
      ∀ᶠ z in 𝓝[>] (-Real.exp (-1)),
        0 < principalLambertW z + 1 := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    linarith [neg_one_lt_principalLambertW hz]
  have hv :
      ∀ᶠ z in 𝓝[>] (-Real.exp (-1)),
        0 < 2 * Real.exp 1 * (z + Real.exp (-1)) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz' : -Real.exp (-1) < z := hz
    exact mul_pos (mul_pos (by norm_num) (Real.exp_pos 1)) (by linarith)
  change
    (fun z : ℝ ↦ principalLambertW z + 1)
      ~[𝓝[>] (-Real.exp (-1))]
        (fun z : ℝ ↦ Real.sqrt
          (2 * Real.exp 1 * (z + Real.exp (-1))))
  exact isEquivalent_sqrt_of_sq (hu.mono fun _ h ↦ h.le)
    (hv.mono fun _ h ↦ h.le)
    principalLambertW_add_one_sq_isEquivalent_branchPoint

/-- Leading lower-branch Puiseux law: the displacement below `-1` is
asymptotic to the negative intrinsic square-root scale. -/
theorem lowerLambertW_add_one_isEquivalent_branchPoint :
    (fun z : ℝ ↦ lowerLambertW z + 1)
      ~[𝓝[>] (-Real.exp (-1))]
        (fun z : ℝ ↦ -lambertWBranchPointScale z) := by
  have hu :
      ∀ᶠ z in 𝓝[>] (-Real.exp (-1)),
        0 < -(lowerLambertW z + 1) := by
    filter_upwards [Ioo_mem_nhdsGT_branchPoint] with z hz
    linarith [lowerLambertW_lt_neg_one hz]
  have hv :
      ∀ᶠ z in 𝓝[>] (-Real.exp (-1)),
        0 < 2 * Real.exp 1 * (z + Real.exp (-1)) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz' : -Real.exp (-1) < z := hz
    exact mul_pos (mul_pos (by norm_num) (Real.exp_pos 1)) (by linarith)
  have hsq :
      (fun z : ℝ ↦ (-(lowerLambertW z + 1)) ^ 2)
        ~[𝓝[>] (-Real.exp (-1))]
          (fun z : ℝ ↦
            2 * Real.exp 1 * (z + Real.exp (-1))) := by
    refine lowerLambertW_add_one_sq_isEquivalent_branchPoint.congr_left ?_
    filter_upwards with z
    ring
  have hmag :
      (fun z : ℝ ↦ -(lowerLambertW z + 1))
        ~[𝓝[>] (-Real.exp (-1))] lambertWBranchPointScale := by
    change
      (fun z : ℝ ↦ -(lowerLambertW z + 1))
        ~[𝓝[>] (-Real.exp (-1))]
          (fun z : ℝ ↦ Real.sqrt
            (2 * Real.exp 1 * (z + Real.exp (-1))))
    exact isEquivalent_sqrt_of_sq (hu.mono fun _ h ↦ h.le)
      (hv.mono fun _ h ↦ h.le) hsq
  simpa only [Pi.neg_apply, neg_neg] using hmag.neg

end

end Fabius
