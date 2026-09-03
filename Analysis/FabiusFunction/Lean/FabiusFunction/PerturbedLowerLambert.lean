import FabiusFunction.LowerLambertW

/-!
# Perturbed lower-Lambert fixed points

This module isolates the algebra behind a periodically perturbed endpoint
saddle.  Let `L > 0`, `x > 0`, and let `C : ℝ → ℝ` be any perturbation.  The
saddle equation

`x * exp (L * u) = u + C u`

becomes a Lambert equation after putting `y = u + C u`:

`(-L * y) * exp (-L * y) = -L * x * exp (-L * C u)`.

Consequently, on the lower branch `1 / L ≤ y`, its solutions are precisely
the fixed points of

`u ↦ -W₋₁(-L * x * exp (-L * C u)) / L - C u`.

Nothing in this argument uses periodicity or a special base.  Taking
`L = log 2` gives the binary endpoint map from the Fabius--Rvachev frontier
report.  The derivative calculation is equally general: if `C'(u) = c`, then
at a lower-branch fixed point the map has derivative

`c / (L * (u + C u) - 1)`.

The branch and natural-domain hypotheses are kept explicit.  In particular,
the defining Lambert equation for the totalized `lowerLambertW` is invoked
only on the interval where that equation is proved.
-/

set_option autoImplicit false

open Set

namespace Fabius

noncomputable section

/-- The Lambert argument associated with an exponentially scaled saddle and
an arbitrary additive perturbation. -/
noncomputable def perturbedLambertArgument
    (L x : ℝ) (C : ℝ → ℝ) (u : ℝ) : ℝ :=
  -L * x * Real.exp (-L * C u)

/-- The lower-Lambert fixed-point map for an arbitrary additive perturbation.

For the binary saddle of the endpoint report, specialize `L` to `log 2`.
The definition is total, but its fixed-point theorems below require the
displayed Lambert argument to lie in the natural lower-branch domain. -/
noncomputable def perturbedLowerLambertMap
    (L x : ℝ) (C : ℝ → ℝ) (u : ℝ) : ℝ :=
  -lowerLambertW (perturbedLambertArgument L x C u) / L - C u

/-- The exponential saddle equation is exactly the Lambert equation for the
shifted coordinate `u + C u`.  This identity is purely algebraic and needs no
sign or branch assumptions. -/
theorem perturbedLambertArgument_eq_mul_exp_of_saddle
    {L x u : ℝ} {C : ℝ → ℝ}
    (hsaddle : x * Real.exp (L * u) = u + C u) :
    perturbedLambertArgument L x C u =
      (-L * (u + C u)) * Real.exp (-L * (u + C u)) := by
  have hexp :
      Real.exp (L * u) * Real.exp (-L * (u + C u)) =
        Real.exp (-L * C u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold perturbedLambertArgument
  rw [← hexp]
  calc
    -L * x *
          (Real.exp (L * u) * Real.exp (-L * (u + C u))) =
        (-L * (x * Real.exp (L * u))) *
          Real.exp (-L * (u + C u)) := by ring
    _ = (-L * (u + C u)) * Real.exp (-L * (u + C u)) := by
      rw [hsaddle]

/-- A positive saddle automatically puts its Lambert argument in the closed
lower-branch domain `[-exp (-1), 0)`.  The lower bound is the global inequality
`y * exp (-y) ≤ exp (-1)`; no branch assumption is needed for this part. -/
theorem perturbedLambertArgument_mem_Ico_of_saddle
    {L x u : ℝ} {C : ℝ → ℝ}
    (hL : 0 < L) (hx : 0 < x)
    (hsaddle : x * Real.exp (L * u) = u + C u) :
    perturbedLambertArgument L x C u ∈
      Ico (-Real.exp (-1)) 0 := by
  rw [perturbedLambertArgument_eq_mul_exp_of_saddle hsaddle]
  have hy : 0 < u + C u := by
    rw [← hsaddle]
    exact mul_pos hx (Real.exp_pos _)
  constructor
  · have hbound := Real.mul_exp_neg_le_exp_neg_one (L * (u + C u))
    calc
      -Real.exp (-1) ≤
          -(L * (u + C u) * Real.exp (-(L * (u + C u)))) :=
        neg_le_neg hbound
      _ = (-L * (u + C u)) * Real.exp (-L * (u + C u)) := by
        ring_nf
  · have hnegative : -L * (u + C u) < 0 :=
      mul_neg_of_neg_of_pos (neg_neg_of_pos hL) hy
    exact mul_neg_of_neg_of_pos hnegative (Real.exp_pos _)

/-- On the lower branch, every positive saddle is a fixed point of the
perturbed lower-Lambert map.  This is the general exponential-rate form of the
periodically perturbed binary Lambert map. -/
theorem perturbedLowerLambertMap_eq_self_of_saddle
    {L x u : ℝ} {C : ℝ → ℝ}
    (hL : 0 < L) (hx : 0 < x)
    (hsaddle : x * Real.exp (L * u) = u + C u)
    (hbranch : 1 / L ≤ u + C u) :
    perturbedLowerLambertMap L x C u = u := by
  have hz := perturbedLambertArgument_mem_Ico_of_saddle hL hx hsaddle
  have hyone : 1 ≤ L * (u + C u) := by
    calc
      1 = L * (1 / L) := by field_simp [hL.ne']
      _ ≤ L * (u + C u) :=
        mul_le_mul_of_nonneg_left hbranch hL.le
  have hw : -L * (u + C u) ≤ -1 := by linarith
  have hW :
      -L * (u + C u) =
        lowerLambertW (perturbedLambertArgument L x C u) :=
    lowerLambertW_unique_of_mem_Ico hz hw
      (perturbedLambertArgument_eq_mul_exp_of_saddle hsaddle).symm
  unfold perturbedLowerLambertMap
  rw [← hW]
  field_simp [hL.ne']
  ring

/-- At any fixed point, the lower Lambert value is the negative scaled shifted
coordinate.  This is the elementary identity used both for the converse
saddle theorem and for the derivative formula. -/
theorem lowerLambertW_perturbedLambertArgument_eq_of_fixed
    {L x u : ℝ} {C : ℝ → ℝ}
    (hL : L ≠ 0)
    (hfixed : perturbedLowerLambertMap L x C u = u) :
    lowerLambertW (perturbedLambertArgument L x C u) =
      -L * (u + C u) := by
  change -lowerLambertW (perturbedLambertArgument L x C u) / L - C u = u
    at hfixed
  calc
    lowerLambertW (perturbedLambertArgument L x C u) =
        -L *
          ((-lowerLambertW (perturbedLambertArgument L x C u) / L - C u) +
            C u) := by
      field_simp [hL]
      ring
    _ = -L * (u + C u) := by rw [hfixed]

/-- A fixed point whose Lambert argument is in the natural domain satisfies
the original exponential saddle equation.  No branch inequality is assumed:
it follows separately from the lower-branch range. -/
theorem saddle_eq_of_perturbedLowerLambertMap_eq_self
    {L x u : ℝ} {C : ℝ → ℝ}
    (hL : L ≠ 0)
    (hz : perturbedLambertArgument L x C u ∈
      Ico (-Real.exp (-1)) 0)
    (hfixed : perturbedLowerLambertMap L x C u = u) :
    x * Real.exp (L * u) = u + C u := by
  have hW :=
    lowerLambertW_perturbedLambertArgument_eq_of_fixed hL hfixed
  have hLambert := lowerLambertW_mul_exp_of_mem_Ico hz
  rw [hW] at hLambert
  have hcancel :
      (u + C u) * Real.exp (-L * (u + C u)) =
        x * Real.exp (-L * C u) := by
    apply mul_left_cancel₀ (a := -L) (neg_ne_zero.mpr hL)
    simpa only [perturbedLambertArgument, mul_assoc] using hLambert
  have hexpForward :
      Real.exp (-L * C u) * Real.exp (L * (u + C u)) =
        Real.exp (L * u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hexpCancel :
      Real.exp (-L * (u + C u)) * Real.exp (L * (u + C u)) = 1 := by
    rw [← Real.exp_add,
      show -L * (u + C u) + L * (u + C u) = 0 by ring,
      Real.exp_zero]
  calc
    x * Real.exp (L * u) =
        x * (Real.exp (-L * C u) * Real.exp (L * (u + C u))) := by
      rw [hexpForward]
    _ = (x * Real.exp (-L * C u)) * Real.exp (L * (u + C u)) := by
      ring
    _ = ((u + C u) * Real.exp (-L * (u + C u))) *
        Real.exp (L * (u + C u)) := by rw [hcancel]
    _ = (u + C u) *
        (Real.exp (-L * (u + C u)) * Real.exp (L * (u + C u))) := by
      ring
    _ = u + C u := by rw [hexpCancel, mul_one]

/-- Every natural-domain fixed point lies on the lower branch
`1 / L ≤ u + C u`. -/
theorem one_div_le_add_of_perturbedLowerLambertMap_eq_self
    {L x u : ℝ} {C : ℝ → ℝ}
    (hL : 0 < L)
    (hz : perturbedLambertArgument L x C u ∈
      Ico (-Real.exp (-1)) 0)
    (hfixed : perturbedLowerLambertMap L x C u = u) :
    1 / L ≤ u + C u := by
  have hWle := lowerLambertW_le_neg_one hz
  rw [lowerLambertW_perturbedLambertArgument_eq_of_fixed hL.ne' hfixed]
    at hWle
  apply (div_le_iff₀ hL).2
  nlinarith

/-- Exact characterization of lower-branch saddles as natural-domain fixed
points of the perturbed lower-Lambert map. -/
theorem perturbedLowerLambertMap_eq_self_iff
    {L x u : ℝ} {C : ℝ → ℝ}
    (hL : 0 < L) (hx : 0 < x)
    (hz : perturbedLambertArgument L x C u ∈
      Ico (-Real.exp (-1)) 0) :
    perturbedLowerLambertMap L x C u = u ↔
      x * Real.exp (L * u) = u + C u ∧ 1 / L ≤ u + C u := by
  constructor
  · intro hfixed
    exact ⟨saddle_eq_of_perturbedLowerLambertMap_eq_self hL.ne' hz hfixed,
      one_div_le_add_of_perturbedLowerLambertMap_eq_self hL hz hfixed⟩
  · rintro ⟨hsaddle, hbranch⟩
    exact perturbedLowerLambertMap_eq_self_of_saddle
      hL hx hsaddle hbranch

/-- Totalized form of the fixed-point characterization.  It records natural
domain membership on the fixed-point side, thereby excluding any spurious
fixed point introduced by the total definition of `lowerLambertW`. -/
theorem perturbedLowerLambertMap_eq_self_and_mem_Ico_iff
    {L x u : ℝ} {C : ℝ → ℝ}
    (hL : 0 < L) (hx : 0 < x) :
    (perturbedLowerLambertMap L x C u = u ∧
        perturbedLambertArgument L x C u ∈
          Ico (-Real.exp (-1)) 0) ↔
      x * Real.exp (L * u) = u + C u ∧ 1 / L ≤ u + C u := by
  constructor
  · rintro ⟨hfixed, hz⟩
    exact (perturbedLowerLambertMap_eq_self_iff hL hx hz).mp hfixed
  · rintro ⟨hsaddle, hbranch⟩
    exact ⟨perturbedLowerLambertMap_eq_self_of_saddle
        hL hx hsaddle hbranch,
      perturbedLambertArgument_mem_Ico_of_saddle hL hx hsaddle⟩

/-- Arbitrary-base form of the fixed-point characterization.  For every
`b > 1`, a lower-branch solution of `x * b ^ u = u + C u` is exactly a fixed
point of the perturbed map with exponential rate `log b`.  The binary report
is the specialization `b = 2`. -/
theorem perturbedLowerLambertMap_log_eq_self_iff_rpow_saddle
    {b x u : ℝ} {C : ℝ → ℝ}
    (hb : 1 < b) (hx : 0 < x)
    (hz : perturbedLambertArgument (Real.log b) x C u ∈
      Ico (-Real.exp (-1)) 0) :
    perturbedLowerLambertMap (Real.log b) x C u = u ↔
      x * b ^ u = u + C u ∧ 1 / Real.log b ≤ u + C u := by
  have hb0 : 0 < b := lt_trans (by norm_num) hb
  simpa only [Real.rpow_def_of_pos hb0] using
    (perturbedLowerLambertMap_eq_self_iff
      (L := Real.log b) (x := x) (u := u) (C := C)
      (Real.log_pos hb) hx hz)

/-- Derivative of the Lambert argument under an arbitrary differentiable
perturbation.  Its logarithmic derivative is simply `-L * c`. -/
theorem perturbedLambertArgument_hasDerivAt
    {L x u c : ℝ} {C : ℝ → ℝ}
    (hC : HasDerivAt C c u) :
    HasDerivAt (perturbedLambertArgument L x C)
      (perturbedLambertArgument L x C u * (-L * c)) u := by
  have hinner : HasDerivAt (fun v : ℝ => -L * C v) (-L * c) u :=
    hC.const_mul (-L)
  have hexp :
      HasDerivAt (fun v : ℝ => Real.exp (-L * C v))
        (Real.exp (-L * C u) * (-L * c)) u :=
    hinner.exp
  change HasDerivAt (fun v : ℝ => perturbedLambertArgument L x C v)
    (perturbedLambertArgument L x C u * (-L * c)) u
  simpa only [perturbedLambertArgument, mul_assoc] using
    hexp.const_mul (-L * x)

/-- Away from the branch point, the perturbed lower-Lambert map has derivative

`-c / (1 + W₋₁(-L * x * exp (-L * C u)))`.

The natural-domain assumption is open because the lower branch is singular at
`-exp (-1)`. -/
theorem perturbedLowerLambertMap_hasDerivAt
    {L x u c : ℝ} {C : ℝ → ℝ}
    (hL : L ≠ 0)
    (hz : perturbedLambertArgument L x C u ∈
      Ioo (-Real.exp (-1)) 0)
    (hC : HasDerivAt C c u) :
    HasDerivAt (perturbedLowerLambertMap L x C)
      (-c /
        (1 + lowerLambertW (perturbedLambertArgument L x C u))) u := by
  let z : ℝ := perturbedLambertArgument L x C u
  let W : ℝ := lowerLambertW z
  have hz' : z ∈ Ioo (-Real.exp (-1)) 0 := by
    simpa only [z] using hz
  have harg :
      HasDerivAt (perturbedLambertArgument L x C)
        (z * (-L * c)) u := by
    simpa only [z] using perturbedLambertArgument_hasDerivAt hC
  have hcomp := (lowerLambertW_hasDerivAt hz').comp u harg
  have hraw := hcomp.neg.div_const L |>.sub hC
  have hWeq : W * Real.exp W = z := by
    simpa only [W] using lowerLambertW_mul_exp hz'
  have hWlt : W < -1 := by
    simpa only [W] using lowerLambertW_lt_neg_one hz'
  have hWone : W + 1 ≠ 0 := by linarith
  have honeW : 1 + W ≠ 0 := by linarith
  have hderiv :
      -((Real.exp W * (W + 1))⁻¹ * (z * (-L * c))) / L - c =
        -c / (1 + W) := by
    rw [← hWeq]
    field_simp [hL, hWone, honeW, Real.exp_ne_zero]
    ring
  exact (hraw.congr_deriv hderiv).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ => rfl)

/-- At a lower-branch fixed point, the derivative takes the intrinsic saddle
form from the periodically perturbed Lambert map:

`C'(u) / (L * (u + C u) - 1)`.

This theorem is stated as a `HasDerivAt`, not merely an equality of `deriv`, so
downstream contraction arguments retain differentiability evidence. -/
theorem perturbedLowerLambertMap_hasDerivAt_of_fixed
    {L x u c : ℝ} {C : ℝ → ℝ}
    (hL : 0 < L)
    (hz : perturbedLambertArgument L x C u ∈
      Ioo (-Real.exp (-1)) 0)
    (hC : HasDerivAt C c u)
    (hfixed : perturbedLowerLambertMap L x C u = u) :
    HasDerivAt (perturbedLowerLambertMap L x C)
      (c / (L * (u + C u) - 1)) u := by
  have hbase := perturbedLowerLambertMap_hasDerivAt hL.ne' hz hC
  have hW :=
    lowerLambertW_perturbedLambertArgument_eq_of_fixed hL.ne' hfixed
  apply hbase.congr_deriv
  rw [hW, show 1 + -L * (u + C u) = -(L * (u + C u) - 1) by ring,
    neg_div_neg_eq]

end

end Fabius
