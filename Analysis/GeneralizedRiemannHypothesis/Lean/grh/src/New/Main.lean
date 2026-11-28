import New.Reduction.OneSidedBound

/-!
# From non-vanishing in Re s > 1/2 to zeros on the critical line

The last step: the usual forms of the hypothesis follow from `DirichletLNonvanishingRightOfHalf`,
the non-vanishing of all Dirichlet L-functions in `re s > 1 / 2`, by the symmetry `s ↦ 1 - s` of the
zeros.

* `New.zeros_on_line`: the zeros of `L(s, χ)` in `0 < re s < 1` have `re s = 1 / 2`.
* `New.zeta_zeros_on_line`: the nontrivial zeros of `ζ` have `re s = 1 / 2`.

## Relation to the literature

Known result: the passage from the half-plane to the critical line by the functional equation. The
non-vanishing itself is `New.grh`.
-/

open Complex DirichletCharacter

variable (h : DirichletLNonvanishingRightOfHalf)

include h

/-- Assume `DirichletLNonvanishingRightOfHalf` (hypothesis `h`): Dirichlet L-functions do not vanish
for Re s > 1/2, the pole excepted. Then `DirichletLZerosOnLine` holds: every zero s of a Dirichlet
L-function with 0 < Re s < 1 has Re s = 1/2. -/
lemma New.zeros_on_line : DirichletLZerosOnLine := by
  intro N _ χ s h_pos h_lt h_zero
  have hs0 : 1 - s ≠ 1 := by aesop
  have hs1 : s ≠ 1 := by aesop
  -- A zero `s` that is not a pole of the gamma factor gives the zero `1 - s` of `L(·, χ⁻¹)`;
  -- the gamma factor has no pole in `0 < re s` (Mathlib gives it the value `0` at a pole).
  have h_gamma : χ.gammaFactor s ≠ 0 := by
    grind [gammaFactor, Gammaℝ_ne_zero_of_re_pos, add_re, one_re]
  have h_zero' : LFunction χ⁻¹ (1 - s) = 0 :=
    (gammaFactor_eq_zero_or_LFunction_one_sub_eq_zero χ s h_pos.ne' hs1 h_zero).resolve_left h_gamma
  -- Neither zero lies to the right of `1 / 2`.
  have h_le : s.re ≤ 1 / 2 := le_of_not_gt fun hlt ↦ h N χ s hlt (.inr hs1) h_zero
  have h_le' : (1 - s).re ≤ 1 / 2 := le_of_not_gt fun hlt ↦ h N χ⁻¹ (1 - s) hlt (.inr hs0) h_zero'
  rw [sub_re, one_re] at h_le'
  linarith

/-- Assume `DirichletLNonvanishingRightOfHalf` (hypothesis `h`): Dirichlet L-functions do not vanish
for Re s > 1/2, the pole excepted. Then `RiemannZetaZerosOnLine` holds: every zero s of ζ outside
{1, −2, −4, …} has Re s = 1/2. -/
lemma New.zeta_zeros_on_line : RiemannZetaZerosOnLine := by
  intro s h_zero h_nontriv hs1
  have hs0 : s ≠ 0 := by grind [riemannZeta_zero]
  -- The poles of `Gammaℝ` are `0, -2, -4, …`, all excluded.
  have h_gamma : Gammaℝ s ≠ 0 := by
    intro h_pole
    obtain ⟨_ | n, rfl⟩ := Gammaℝ_eq_zero_iff.1 h_pole <;> grind
  -- So `s` is a zero of the completed zeta function, which is symmetric under `s ↦ 1 - s`.
  have h_completed : completedRiemannZeta s = 0 := by
    simpa [riemannZeta_def_of_ne_zero hs0, h_gamma] using h_zero
  have h_zero' : riemannZeta (1 - s) = 0 := by
    simp [riemannZeta_def_of_ne_zero (sub_ne_zero.2 hs1.symm), completedRiemannZeta_one_sub,
      h_completed]
  -- ζ is the L-function of the character modulo `1`: neither zero lies to the right of `1 / 2`.
  have h_le (z : ℂ) (hz1 : z ≠ 1) (hz : riemannZeta z = 0) : z.re ≤ 1 / 2 :=
    le_of_not_gt fun hlt ↦ h 1 1 z hlt (.inr hz1) (by simpa using hz)
  have h_upper : s.re ≤ 1 / 2 := h_le s hs1 h_zero
  have h_lower : 1 - s.re ≤ 1 / 2 := by simpa using h_le (1 - s) (by simpa using hs0) h_zero'
  linarith
