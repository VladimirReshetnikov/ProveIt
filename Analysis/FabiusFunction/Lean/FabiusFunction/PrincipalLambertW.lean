import FabiusFunction.LowerLambertW

/-!
# The principal real Lambert branch

The corpus carries the lower real Lambert branch `W₋₁`
(`LowerLambertW.lean`); this module supplies its companion, the
principal branch `W₀` on `[-e⁻¹, ∞)`, by the same construction: `W₀`
is the logarithm of the inverse of `u ↦ u·log u` on `[e⁻¹, ∞)`, where
that map is strictly increasing.

* `principalLambertW_mul_exp` — the defining equation
  `W₀(z)·e^{W₀(z)} = z` on `[-e⁻¹, ∞)`;
* `neg_one_le_principalLambertW` — the branch stays at or above `-1`;
* `principalLambertW_unique` — uniqueness among solutions `≥ -1`;
* branch point `W₀(-e⁻¹) = -1`, `W₀(0) = 0`, `W₀(e) = 1`;
* `principalLambertW_strictMonoOn` — strict monotonicity.

Together with the lower branch this completes the real Lambert pair —
the subject of the `lambert-w` draft group and the function behind
the corpus's two-scale endpoint asymptotics.
-/

set_option autoImplicit false

open Set Function

namespace Fabius

noncomputable section

private def mulLogP (u : ℝ) : ℝ := u * Real.log u

private lemma exists_mulLogP_eq {z : ℝ} (hz : -Real.exp (-1) ≤ z) :
    ∃ u ∈ Ici (Real.exp (-1)), mulLogP u = z := by
  have hle : Real.exp (-1) ≤ Real.exp (max 1 z) :=
    Real.exp_le_exp.mpr (by
      have := le_max_left 1 z
      linarith)
  have hcont : ContinuousOn mulLogP
      (Icc (Real.exp (-1)) (Real.exp (max 1 z))) :=
    Real.continuous_mul_log.continuousOn
  have hlo : mulLogP (Real.exp (-1)) = -Real.exp (-1) := by
    simp [mulLogP]
  have hone : (1 : ℝ) ≤ Real.exp (max 1 z) := by
    have h := Real.exp_le_exp.mpr
      (le_trans zero_le_one (le_max_left 1 z) : (0 : ℝ) ≤ max 1 z)
    rwa [Real.exp_zero] at h
  have hhi : z ≤ mulLogP (Real.exp (max 1 z)) := by
    have hval : mulLogP (Real.exp (max 1 z)) =
        max 1 z * Real.exp (max 1 z) := by
      simp [mulLogP, Real.log_exp, mul_comm]
    rw [hval]
    calc z ≤ max 1 z := le_max_right _ _
      _ = max 1 z * 1 := (mul_one _).symm
      _ ≤ max 1 z * Real.exp (max 1 z) := by
          refine mul_le_mul_of_nonneg_left hone ?_
          exact le_trans zero_le_one (le_max_left _ _)
  have hz' : z ∈ Icc (mulLogP (Real.exp (-1)))
      (mulLogP (Real.exp (max 1 z))) := ⟨hlo ▸ hz, hhi⟩
  obtain ⟨u, hu, huz⟩ := intermediate_value_Icc hle hcont hz'
  exact ⟨u, hu.1, huz⟩

/-- The argument whose logarithm is the principal real Lambert
branch. -/
noncomputable def principalLambertArg (z : ℝ) : ℝ :=
  Function.invFunOn mulLogP (Ici (Real.exp (-1))) z

/-- A totalized definition of the principal real Lambert branch.  Its
intended domain is `[-e⁻¹, ∞)`. -/
noncomputable def principalLambertW (z : ℝ) : ℝ :=
  Real.log (principalLambertArg z)

private lemma principalLambertArg_spec {z : ℝ}
    (hz : -Real.exp (-1) ≤ z) :
    principalLambertArg z ∈ Ici (Real.exp (-1)) ∧
      mulLogP (principalLambertArg z) = z := by
  obtain ⟨u, hu, huz⟩ := exists_mulLogP_eq hz
  have hspec0 := Function.invFunOn_pos ⟨u, hu, huz⟩
  simpa [principalLambertArg] using hspec0

/-- **The defining equation** `W₀(z)·e^{W₀(z)} = z` on `[-e⁻¹, ∞)`. -/
theorem principalLambertW_mul_exp {z : ℝ} (hz : -Real.exp (-1) ≤ z) :
    principalLambertW z * Real.exp (principalLambertW z) = z := by
  obtain ⟨hmem, heq⟩ := principalLambertArg_spec hz
  have hupos : 0 < principalLambertArg z :=
    lt_of_lt_of_le (Real.exp_pos _) hmem
  rw [principalLambertW, Real.exp_log hupos, mul_comm]
  exact heq

/-- The principal branch stays at or above `-1`. -/
theorem neg_one_le_principalLambertW {z : ℝ}
    (hz : -Real.exp (-1) ≤ z) :
    -1 ≤ principalLambertW z := by
  have hmem := (principalLambertArg_spec hz).1
  rw [principalLambertW,
    show (-1 : ℝ) = Real.log (Real.exp (-1)) from
      (Real.log_exp _).symm]
  exact (Real.log_le_log_iff (Real.exp_pos _)
    (lt_of_lt_of_le (Real.exp_pos _) hmem)).mpr hmem

/-- **Uniqueness** among solutions at or above `-1`. -/
theorem principalLambertW_unique {z w : ℝ} (hz : -Real.exp (-1) ≤ z)
    (hw : -1 ≤ w) (hwz : w * Real.exp w = z) :
    w = principalLambertW z := by
  have hu : Real.exp w ∈ Ici (Real.exp (-1)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hval : mulLogP (Real.exp w) = z := by
    rw [mulLogP, Real.log_exp, mul_comm]
    exact hwz
  obtain ⟨hmem, heq⟩ := principalLambertArg_spec hz
  have hinj := Real.mul_log_strictMonoOn.injOn hu hmem
    (by
      show mulLogP (Real.exp w) = mulLogP (principalLambertArg z)
      rw [hval, heq])
  rw [principalLambertW, ← hinj, Real.log_exp]

/-- At the branch point, the principal branch has value `-1`. -/
@[simp] theorem principalLambertW_branchPoint :
    principalLambertW (-Real.exp (-1)) = -1 :=
  (principalLambertW_unique le_rfl le_rfl (by
    rw [neg_one_mul])).symm

/-- The principal Lambert branch sends zero to zero. -/
@[simp] theorem principalLambertW_zero : principalLambertW 0 = 0 :=
  (principalLambertW_unique (neg_nonpos.mpr (Real.exp_pos _).le)
    (by norm_num) (by simp)).symm

/-- `W₀(e) = 1`. -/
theorem principalLambertW_exp_one :
    principalLambertW (Real.exp 1) = 1 :=
  (principalLambertW_unique
    (le_trans (neg_nonpos.mpr (Real.exp_pos _).le)
      (Real.exp_pos _).le)
    (by norm_num) (one_mul _)).symm

/-- The forward map `t ↦ t·eᵗ` is strictly increasing on
`[-1, ∞)`. -/
theorem mul_exp_strictMonoOn :
    StrictMonoOn (fun t : ℝ => t * Real.exp t) (Ici (-1 : ℝ)) := by
  intro s hs t ht hst
  have hms : Real.exp s ∈ Ici (Real.exp (-1)) := Real.exp_le_exp.mpr hs
  have hmt : Real.exp t ∈ Ici (Real.exp (-1)) := Real.exp_le_exp.mpr ht
  have h := Real.mul_log_strictMonoOn hms hmt
    (Real.exp_lt_exp.mpr hst)
  simpa [Real.log_exp, mul_comm] using h

/-- The principal branch is strictly increasing on its domain. -/
theorem principalLambertW_strictMonoOn :
    StrictMonoOn principalLambertW (Ici (-Real.exp (-1))) := by
  intro a ha b hb hab
  by_contra hcon
  push_neg at hcon
  have h1 := principalLambertW_mul_exp (mem_Ici.mp ha)
  have h2 := principalLambertW_mul_exp (mem_Ici.mp hb)
  have hWa := neg_one_le_principalLambertW (mem_Ici.mp ha)
  have hWb := neg_one_le_principalLambertW (mem_Ici.mp hb)
  have hmono := mul_exp_strictMonoOn.monotoneOn
    (mem_Ici.mpr hWb) (mem_Ici.mpr hWa) hcon
  rw [h1, h2] at hmono
  linarith

/-- Above the branch point the branch exceeds `-1`. -/
theorem neg_one_lt_principalLambertW {z : ℝ}
    (hz : -Real.exp (-1) < z) :
    -1 < principalLambertW z := by
  have h := principalLambertW_strictMonoOn (mem_Ici.mpr le_rfl)
    (mem_Ici.mpr hz.le) hz
  rwa [principalLambertW_branchPoint] at h

/-- Exact image of the open domain: `W₀ '' (-e⁻¹, ∞) = (-1, ∞)`. -/
theorem principalLambertW_image_Ioi :
    principalLambertW '' Ioi (-Real.exp (-1)) = Ioi (-1 : ℝ) := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact neg_one_lt_principalLambertW hz
  · intro hw
    have hgt : -Real.exp (-1) < w * Real.exp w := by
      have h := mul_exp_strictMonoOn (mem_Ici.mpr le_rfl)
        (mem_Ici.mpr (le_of_lt hw)) hw
      simpa [neg_one_mul] using h
    exact ⟨w * Real.exp w, hgt,
      (principalLambertW_unique hgt.le (le_of_lt hw) rfl).symm⟩

/-- The principal branch is continuous at every point of the open
domain. -/
theorem principalLambertW_continuousAt {z : ℝ}
    (hz : -Real.exp (-1) < z) :
    ContinuousAt principalLambertW z := by
  have hmono : StrictMonoOn principalLambertW
      (Ioi (-Real.exp (-1))) := fun a ha b hb hab =>
    principalLambertW_strictMonoOn (mem_Ici.mpr (le_of_lt ha))
      (mem_Ici.mpr (le_of_lt hb)) hab
  exact hmono.continuousAt_of_image_mem_nhds
    (isOpen_Ioi.mem_nhds hz) (by
      rw [principalLambertW_image_Ioi]
      exact Ioi_mem_nhds (neg_one_lt_principalLambertW hz))

/-- Continuity of the principal branch on the open domain. -/
theorem principalLambertW_continuousOn :
    ContinuousOn principalLambertW (Ioi (-Real.exp (-1))) :=
  fun _ hz => (principalLambertW_continuousAt hz).continuousWithinAt

/-- Inverse-function derivative of the principal branch. -/
theorem principalLambertW_hasDerivAt {z : ℝ}
    (hz : -Real.exp (-1) < z) :
    HasDerivAt principalLambertW
      (Real.exp (principalLambertW z) *
        (principalLambertW z + 1))⁻¹ z := by
  have hf : HasDerivAt (fun w : ℝ => w * Real.exp w)
      (Real.exp (principalLambertW z) * (principalLambertW z + 1))
      (principalLambertW z) := by
    have h0 := (hasDerivAt_id (principalLambertW z)).mul
      (Real.hasDerivAt_exp (principalLambertW z))
    have hfun : (fun w : ℝ => w * Real.exp w)
        =ᶠ[nhds (principalLambertW z)] (id * Real.exp) :=
      Filter.Eventually.of_forall fun w => by
        simp only [Pi.mul_apply, id_eq]
    exact (h0.congr_of_eventuallyEq hfun).congr_deriv (by
      simp only [id_eq]
      ring_nf)
  have hW := neg_one_lt_principalLambertW hz
  have hderiv : Real.exp (principalLambertW z) *
      (principalLambertW z + 1) ≠ 0 :=
    mul_ne_zero (Real.exp_ne_zero _) (by linarith)
  have hinverse : ∀ᶠ y in nhds z,
      principalLambertW y * Real.exp (principalLambertW y) = y := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
    exact principalLambertW_mul_exp (le_of_lt hy)
  exact hf.of_local_left_inverse
    (principalLambertW_continuousAt hz) hderiv hinverse

/-- The derivative of the principal branch is strictly positive on
the open domain. -/
theorem deriv_principalLambertW_pos {z : ℝ}
    (hz : -Real.exp (-1) < z) :
    0 < deriv principalLambertW z := by
  rw [(principalLambertW_hasDerivAt hz).deriv]
  have hW := neg_one_lt_principalLambertW hz
  exact inv_pos.mpr (mul_pos (Real.exp_pos _) (by linarith))

end

end Fabius
