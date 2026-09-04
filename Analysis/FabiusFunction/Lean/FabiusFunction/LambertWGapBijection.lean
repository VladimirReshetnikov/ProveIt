import FabiusFunction.LambertBranchDichotomy
import FabiusFunction.LambertWBranchPairing

/-!
# The branch gap is a bijection onto `(0, ∞)`

`LambertWBranchPairing` writes both real branches at `x ∈ (-1/e, 0)` through
the gap `Δ = W₀(x) - W₋₁(x) > 0`:

`W₀(x) = -Δ/(e^Δ - 1)`,  `W₋₁(x) = -Δ e^Δ/(e^Δ - 1)`,  `x = W₀(x) e^{W₀(x)}`.

This module proves the Lambert W guide's converse: every `Δ > 0`, inserted
into these formulas, produces one and only one `x ∈ (-1/e, 0)`, and the
displayed values are its two branches.  Together the two directions say that
the gap `x ↦ W₀(x) - W₋₁(x)` is a bijection from `(-1/e, 0)` onto `(0, ∞)`,
with the explicit inverse `Δ ↦ a(Δ) e^{a(Δ)}`, `a(Δ) = -Δ/(e^Δ - 1)`.

## The mechanism

Put `a(Δ) = -Δ/(e^Δ - 1)` and `b(Δ) = a(Δ) e^Δ`.  Then `b = a - Δ` (a
one-line identity), so `b e^b = a e^Δ e^{a - Δ} = a e^a`: the two numbers are
two preimages of `x = a e^a` under `w ↦ w e^w`.  Since `-1 < a < 0` (that is
`Δ < e^Δ - 1`) and `b < -1` (that is `e^Δ (1 - Δ) < 1`), the uniqueness
theorems of the two branches identify `a = W₀(x)` and `b = W₋₁(x)`, so the
gap of `x` is `a - b = Δ`.  Injectivity of the gap is the forward formula
`x = a(Δ) e^{a(Δ)}` already proved in `LambertWBranchPairing`.
-/

set_option autoImplicit false

open Set

namespace Fabius

/-- The principal value written through the gap: `a(Δ) = -Δ/(e^Δ - 1)`. -/
noncomputable def gapPrincipal (Δ : ℝ) : ℝ := -Δ / (Real.exp Δ - 1)

/-- The lower value written through the gap: `b(Δ) = -Δ e^Δ/(e^Δ - 1)`. -/
noncomputable def gapLower (Δ : ℝ) : ℝ := -Δ * Real.exp Δ / (Real.exp Δ - 1)

/-- The argument written through the gap: `x(Δ) = a(Δ) e^{a(Δ)}`. -/
noncomputable def gapArg (Δ : ℝ) : ℝ := gapPrincipal Δ * Real.exp (gapPrincipal Δ)

/-- The branch gap `Δ(x) = W₀(x) - W₋₁(x)`. -/
noncomputable def branchGap (x : ℝ) : ℝ := principalLambertW x - lowerLambertW x

/-- The common denominator `e^Δ - 1` is positive for `Δ > 0`. -/
theorem gap_denominator_pos {Δ : ℝ} (hΔ : 0 < Δ) : 0 < Real.exp Δ - 1 := by
  have := Real.add_one_lt_exp hΔ.ne'
  linarith

/-- `-1 < a(Δ) < 0` for `Δ > 0`; the lower bound is `Δ < e^Δ - 1`. -/
theorem gapPrincipal_mem_Ioo {Δ : ℝ} (hΔ : 0 < Δ) : gapPrincipal Δ ∈ Ioo (-1 : ℝ) 0 := by
  have hden := gap_denominator_pos hΔ
  have hlt := Real.add_one_lt_exp hΔ.ne'
  constructor
  · rw [gapPrincipal, lt_div_iff₀ hden]
    linarith
  · exact div_neg_of_neg_of_pos (by linarith) hden

/-- `b(Δ) = a(Δ) e^Δ`. -/
theorem gapLower_eq_mul_exp (Δ : ℝ) : gapLower Δ = gapPrincipal Δ * Real.exp Δ := by
  unfold gapLower gapPrincipal
  ring

/-- `b(Δ) = a(Δ) - Δ`: the two values differ by exactly `Δ`. -/
theorem gapLower_eq_sub {Δ : ℝ} (hΔ : 0 < Δ) : gapLower Δ = gapPrincipal Δ - Δ := by
  have hden := (gap_denominator_pos hΔ).ne'
  unfold gapLower gapPrincipal
  field_simp; ring

/-- `b(Δ) < -1` for `Δ > 0`; this is `e^Δ (1 - Δ) < 1`, the tangent-line
inequality at `-Δ`. -/
theorem gapLower_lt_neg_one {Δ : ℝ} (hΔ : 0 < Δ) : gapLower Δ < -1 := by
  have hden := gap_denominator_pos hΔ
  have h1 : -Δ + 1 < Real.exp (-Δ) := Real.add_one_lt_exp (neg_ne_zero.mpr hΔ.ne')
  have h2 : Real.exp Δ * (1 - Δ) < 1 := by
    have hE := Real.exp_pos Δ
    have := mul_lt_mul_of_pos_left h1 hE
    rw [Real.exp_neg, mul_inv_cancel₀ hE.ne'] at this
    linarith
  rw [gapLower, div_lt_iff₀ hden]
  linarith

/-- `b(Δ)` satisfies the defining equation at `x(Δ)`: `b e^b = a e^a`. -/
theorem gapLower_mul_exp {Δ : ℝ} (hΔ : 0 < Δ) :
    gapLower Δ * Real.exp (gapLower Δ) = gapArg Δ := by
  have hE := (Real.exp_pos Δ).ne'
  calc gapLower Δ * Real.exp (gapLower Δ)
      = (gapPrincipal Δ * Real.exp Δ) * Real.exp (gapPrincipal Δ - Δ) := by
        rw [← gapLower_eq_mul_exp, ← gapLower_eq_sub hΔ]
    _ = gapArg Δ := by
        rw [Real.exp_sub, gapArg]
        field_simp

/-- `x(Δ) ∈ (-1/e, 0)` for `Δ > 0`.  Strictness at `-1/e` comes from
uniqueness: equality would force `a(Δ) = W₀(-1/e) = -1`. -/
theorem gapArg_mem_Ioo {Δ : ℝ} (hΔ : 0 < Δ) : gapArg Δ ∈ Ioo (-Real.exp (-1)) 0 := by
  obtain ⟨ha1, ha0⟩ := gapPrincipal_mem_Ioo hΔ
  unfold gapArg
  refine ⟨?_, mul_neg_of_neg_of_pos ha0 (Real.exp_pos _)⟩
  refine lt_of_le_of_ne (neg_exp_neg_one_le_mul_exp _) fun heq => ?_
  have hm1 : (-1 : ℝ) = principalLambertW (-Real.exp (-1)) :=
    principalLambertW_unique le_rfl le_rfl (by ring)
  have ha : gapPrincipal Δ = principalLambertW (-Real.exp (-1)) :=
    principalLambertW_unique le_rfl ha1.le heq.symm
  linarith

/-- **The principal branch at `x(Δ)`** is `a(Δ)`. -/
theorem principalLambertW_gapArg {Δ : ℝ} (hΔ : 0 < Δ) :
    principalLambertW (gapArg Δ) = gapPrincipal Δ :=
  (principalLambertW_unique (gapArg_mem_Ioo hΔ).1.le (gapPrincipal_mem_Ioo hΔ).1.le rfl).symm

/-- **The lower branch at `x(Δ)`** is `b(Δ)`. -/
theorem lowerLambertW_gapArg {Δ : ℝ} (hΔ : 0 < Δ) :
    lowerLambertW (gapArg Δ) = gapLower Δ :=
  (lowerLambertW_unique_of_mem_Ico ⟨(gapArg_mem_Ioo hΔ).1.le, (gapArg_mem_Ioo hΔ).2⟩
    (gapLower_lt_neg_one hΔ).le (gapLower_mul_exp hΔ)).symm

/-- **The gap of `x(Δ)` is `Δ`**: the converse half of the pairing theorem. -/
theorem branchGap_gapArg {Δ : ℝ} (hΔ : 0 < Δ) : branchGap (gapArg Δ) = Δ := by
  rw [branchGap, principalLambertW_gapArg hΔ, lowerLambertW_gapArg hΔ, gapLower_eq_sub hΔ]
  ring

/-- **The argument from its gap**: `x = x(Δ(x))` on `(-1/e, 0)`; this is the
forward formula of `LambertWBranchPairing`. -/
theorem gapArg_branchGap {x : ℝ} (hx : x ∈ Ioo (-Real.exp (-1)) 0) :
    gapArg (branchGap x) = x :=
  (eq_neg_gap_div_mul_exp hx).symm

/-- The gap and `gapArg` are two-sided inverses between `(-1/e, 0)` and `(0, ∞)`. -/
theorem branchGap_invOn : InvOn gapArg branchGap (Ioo (-Real.exp (-1)) 0) (Ioi 0) :=
  ⟨fun _ hx => gapArg_branchGap hx, fun _ hΔ => branchGap_gapArg hΔ⟩

/-- **The gap is a bijection** from `(-1/e, 0)` onto `(0, ∞)`: every positive
gap is attained at exactly one argument. -/
theorem branchGap_bijOn : BijOn branchGap (Ioo (-Real.exp (-1)) 0) (Ioi 0) :=
  branchGap_invOn.bijOn (fun _ hx => principalLambertW_sub_lowerLambertW_pos hx)
    (fun _ hΔ => gapArg_mem_Ioo hΔ)

end Fabius
