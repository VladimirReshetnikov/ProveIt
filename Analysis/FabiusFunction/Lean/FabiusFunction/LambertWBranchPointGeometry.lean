import FabiusFunction.LambertWCurvature

/-!
# Branch-point geometry of the real Lambert branches

The two real Lambert branches meet at `-exp (-1)` with value `-1`.  This
module closes the corresponding vertical-tangent statements.  Approaching
the branch point from the right, the derivative of the principal branch
diverges to positive infinity, while the derivative of the lower branch
diverges to negative infinity.  The same limits hold for the endpoint
secant slopes, and in particular neither totalized branch is differentiable
at the branch point.

The proofs use only the endpoint continuity, inverse-function derivative,
and curvature APIs.  No square-root or Puiseux expansion is needed.

Two small filter facts about the right neighbourhood of the branch point
(`Ioo_mem_nhdsGT_branchPoint`, `nhdsGT_branchPoint_le_nhdsWithin_Ico`)
are recorded first; the asymptotics module reuses them.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Fabius

noncomputable section

/-! ## Right neighbourhoods of the branch point -/

/-- The open lower-branch domain `(-e⁻¹, 0)` is a right neighbourhood of
the branch point. -/
theorem Ioo_mem_nhdsGT_branchPoint :
    Ioo (-Real.exp (-1)) 0 ∈ 𝓝[>] (-Real.exp (-1)) :=
  Ioo_mem_nhdsGT (neg_lt_zero.mpr (Real.exp_pos (-1)))

/-- The right filter at the branch point refines the within-filter of
the closed-left lower-branch domain `[-e⁻¹, 0)`. -/
theorem nhdsGT_branchPoint_le_nhdsWithin_Ico :
    𝓝[>] (-Real.exp (-1)) ≤
      𝓝[Ico (-Real.exp (-1)) 0] (-Real.exp (-1)) := by
  rw [nhdsWithin_le_iff]
  exact Filter.mem_of_superset Ioo_mem_nhdsGT_branchPoint
    Ioo_subset_Ico_self

/-! ## Infinite one-sided derivatives -/

/-- The derivative of the principal Lambert branch diverges to positive
infinity as its argument approaches the real branch point from the right. -/
theorem tendsto_deriv_principalLambertW_branchPoint_atTop :
    Tendsto (deriv principalLambertW)
      (nhdsWithin (-Real.exp (-1)) (Ioi (-Real.exp (-1)))) atTop := by
  let D : ℝ → ℝ := fun z ↦
    Real.exp (principalLambertW z) * (principalLambertW z + 1)
  have hWclosed :
      Tendsto principalLambertW
        (nhdsWithin (-Real.exp (-1)) (Ici (-Real.exp (-1))))
        (nhds (-1 : ℝ)) := by
    simpa only [principalLambertW_branchPoint] using
      principalLambertW_continuousWithinAt_branchPoint.tendsto
  have hW :
      Tendsto principalLambertW
        (nhdsWithin (-Real.exp (-1)) (Ioi (-Real.exp (-1))))
        (nhds (-1 : ℝ)) :=
    hWclosed.mono_left
      (nhdsWithin_mono _ Ioi_subset_Ici_self)
  have hD0 :
      Tendsto D
        (nhdsWithin (-Real.exp (-1)) (Ioi (-Real.exp (-1))))
        (nhds (0 : ℝ)) := by
    have h := hW.rexp.mul (hW.add_const 1)
    simpa [D] using h
  have hD :
      Tendsto D
        (nhdsWithin (-Real.exp (-1)) (Ioi (-Real.exp (-1))))
        (nhdsWithin (0 : ℝ) (Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hD0, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact mul_pos (Real.exp_pos _) (by
      linarith [neg_one_lt_principalLambertW hz])
  refine hD.inv_tendsto_nhdsGT_zero.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (principalLambertW_hasDerivAt hz).deriv.symm

/-- The derivative of the lower Lambert branch diverges to negative infinity
as its argument approaches the real branch point from the right. -/
theorem tendsto_deriv_lowerLambertW_branchPoint_atBot :
    Tendsto (deriv lowerLambertW)
      (nhdsWithin (-Real.exp (-1)) (Ioi (-Real.exp (-1)))) atBot := by
  let D : ℝ → ℝ := fun z ↦
    Real.exp (lowerLambertW z) * (lowerLambertW z + 1)
  have hWclosed :
      Tendsto lowerLambertW
        (nhdsWithin (-Real.exp (-1))
          (Ico (-Real.exp (-1)) 0))
        (nhds (-1 : ℝ)) := by
    simpa only [lowerLambertW_branchPoint] using
      lowerLambertW_continuousWithinAt_branchPoint.tendsto
  have hW :
      Tendsto lowerLambertW
        (nhdsWithin (-Real.exp (-1)) (Ioi (-Real.exp (-1))))
        (nhds (-1 : ℝ)) :=
    hWclosed.mono_left nhdsGT_branchPoint_le_nhdsWithin_Ico
  have hD0 :
      Tendsto D
        (nhdsWithin (-Real.exp (-1)) (Ioi (-Real.exp (-1))))
        (nhds (0 : ℝ)) := by
    have h := hW.rexp.mul (hW.add_const 1)
    simpa [D] using h
  have hD :
      Tendsto D
        (nhdsWithin (-Real.exp (-1)) (Ioi (-Real.exp (-1))))
        (nhdsWithin (0 : ℝ) (Iio 0)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hD0, ?_⟩
    filter_upwards [Ioo_mem_nhdsGT_branchPoint] with z hz
    exact mul_neg_of_pos_of_neg (Real.exp_pos _) (by
      linarith [lowerLambertW_lt_neg_one hz])
  refine hD.inv_tendsto_nhdsLT_zero.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT_branchPoint] with z hz
  exact (lowerLambertW_hasDerivAt hz).deriv.symm

/-! ## Endpoint secant slopes -/

/-- The secant slopes from the branch point to the principal branch diverge
to positive infinity.  This is the endpoint-slope form of its vertical
tangent. -/
theorem tendsto_principalLambertW_secantSlope_branchPoint_atTop :
    Tendsto
      (fun z : ℝ ↦
        (principalLambertW z + 1) / (z + Real.exp (-1)))
      (nhdsWithin (-Real.exp (-1)) (Ioi (-Real.exp (-1)))) atTop := by
  refine tendsto_atTop_mono' _ ?_
    tendsto_deriv_principalLambertW_branchPoint_atTop
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hslope :
      deriv principalLambertW z ≤
        slope principalLambertW (-Real.exp (-1)) z :=
    strictConcaveOn_principalLambertW.concaveOn.deriv_le_slope
      (mem_Ici.mpr le_rfl) (mem_Ici.mpr hz.le) hz
      (principalLambertW_hasDerivAt hz).differentiableAt
  simpa only [slope_def_field, principalLambertW_branchPoint,
    sub_neg_eq_add] using hslope

private lemma branchPoint_lt_lowerInflection :
    -Real.exp (-1) < -2 * Real.exp (-2) := by
  linarith [two_mul_exp_neg_two_lt_exp_neg_one]

/-- The secant slopes from the branch point to the lower branch diverge to
negative infinity.  This is the endpoint-slope form of its vertical
tangent. -/
theorem tendsto_lowerLambertW_secantSlope_branchPoint_atBot :
    Tendsto
      (fun z : ℝ ↦
        (lowerLambertW z + 1) / (z + Real.exp (-1)))
      (nhdsWithin (-Real.exp (-1)) (Ioi (-Real.exp (-1)))) atBot := by
  refine tendsto_atBot_mono' _ ?_
    tendsto_deriv_lowerLambertW_branchPoint_atBot
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds branchPoint_lt_lowerInflection)] with z hz hzInf
  have hInf0 : -2 * Real.exp (-2) < (0 : ℝ) :=
    mul_neg_of_neg_of_pos (by norm_num) (Real.exp_pos _)
  have hz0 : z < 0 := hzInf.trans hInf0
  have hslope :
      slope lowerLambertW (-Real.exp (-1)) z ≤
        deriv lowerLambertW z :=
    strictConvexOn_lowerLambertW_left.convexOn.slope_le_deriv
      ⟨le_rfl, branchPoint_lt_lowerInflection.le⟩
      ⟨hz.le, hzInf.le⟩ hz
      (lowerLambertW_hasDerivAt ⟨hz, hz0⟩).differentiableAt
  simpa only [slope_def_field, lowerLambertW_branchPoint,
    sub_neg_eq_add] using hslope

/-! ## Failure of finite differentiability -/

/-- The principal Lambert branch has no finite right derivative at the
branch point. -/
theorem principalLambertW_not_differentiableWithinAt_branchPoint :
    ¬ DifferentiableWithinAt ℝ principalLambertW
      (Ioi (-Real.exp (-1))) (-Real.exp (-1)) :=
  not_differentiableWithinAt_of_deriv_tendsto_atTop_Ioi
    principalLambertW tendsto_deriv_principalLambertW_branchPoint_atTop

/-- The lower Lambert branch has no finite right derivative at the branch
point. -/
theorem lowerLambertW_not_differentiableWithinAt_branchPoint :
    ¬ DifferentiableWithinAt ℝ lowerLambertW
      (Ioi (-Real.exp (-1))) (-Real.exp (-1)) :=
  not_differentiableWithinAt_of_deriv_tendsto_atBot_Ioi
    lowerLambertW tendsto_deriv_lowerLambertW_branchPoint_atBot

/-- The totalized principal Lambert branch is not differentiable at the real
branch point. -/
theorem principalLambertW_not_differentiableAt_branchPoint :
    ¬ DifferentiableAt ℝ principalLambertW (-Real.exp (-1)) := by
  intro h
  exact principalLambertW_not_differentiableWithinAt_branchPoint
    h.differentiableWithinAt

/-- The totalized lower Lambert branch is not differentiable at the real
branch point. -/
theorem lowerLambertW_not_differentiableAt_branchPoint :
    ¬ DifferentiableAt ℝ lowerLambertW (-Real.exp (-1)) := by
  intro h
  exact lowerLambertW_not_differentiableWithinAt_branchPoint
    h.differentiableWithinAt

end

end Fabius
