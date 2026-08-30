import FabiusFunction.FabiusInverse
import FabiusFunction.MidpointEndpointTransfer

/-!
# Exact inverse midpoint defect

The midpoint--endpoint transmutation converts the inverse Fabius function
near its reflection-fixed midpoint into an exact scalar fixed-point problem.
For a vertical displacement `δ`, define

`h(δ) = F⁻¹(1 / 2 + δ) - 1 / 2`

and remove the affine inverse jet by

`E(δ) = h(δ) - δ / 2`.

On `0 ≤ δ ≤ 1 / 2` the transmutation gives

`δ = 2h - F(h)`,  `h = δ / 2 + F(h) / 2`,  and
`E = F(δ / 2 + E) / 2`.

The offset and defect are globally odd because the totalized inverse inherits
reflection symmetry.  This file proves only that exact finite layer.  It does
not infer all-orders flatness, an asymptotic equivalence, a logarithmic
expansion, or a Lambert--W transfer from the fixed-point equation alone.
-/

set_option autoImplicit false

open Set

namespace Fabius

noncomputable section

/-- Horizontal displacement of the inverse Fabius graph from its midpoint. -/
def fabiusInvMidpointOffset
    (F : BoundedFabius) (hF : IsFabius F) (δ : ℝ) : ℝ :=
  fabiusInv F hF (1 / 2 + δ) - 1 / 2

/-- Exact defect left after removing the affine inverse midpoint jet `δ / 2`
from `fabiusInvMidpointOffset`.  No asymptotic estimate is built into the
definition. -/
def fabiusInvMidpointDefect
    (F : BoundedFabius) (hF : IsFabius F) (δ : ℝ) : ℝ :=
  fabiusInvMidpointOffset F hF δ - δ / 2

/-- The inverse midpoint offset vanishes at zero. -/
@[simp] theorem fabiusInvMidpointOffset_zero
    (F : BoundedFabius) (hF : IsFabius F) :
    fabiusInvMidpointOffset F hF 0 = 0 := by
  norm_num [fabiusInvMidpointOffset, fabiusInv_half F hF]

/-- The inverse midpoint defect vanishes at zero. -/
@[simp] theorem fabiusInvMidpointDefect_zero
    (F : BoundedFabius) (hF : IsFabius F) :
    fabiusInvMidpointDefect F hF 0 = 0 := by
  norm_num [fabiusInvMidpointDefect]

/-- At the upper endpoint of the central inverse half-cell, the horizontal
offset is exactly `1 / 2`. -/
@[simp] theorem fabiusInvMidpointOffset_half
    (F : BoundedFabius) (hF : IsFabius F) :
    fabiusInvMidpointOffset F hF (1 / 2) = 1 / 2 := by
  norm_num [fabiusInvMidpointOffset, fabiusInv_one F hF]

/-- The upper bound `1 / 4` for the positive inverse midpoint defect is
attained when `δ = 1 / 2`. -/
@[simp] theorem fabiusInvMidpointDefect_half
    (F : BoundedFabius) (hF : IsFabius F) :
    fabiusInvMidpointDefect F hF (1 / 2) = 1 / 4 := by
  norm_num [fabiusInvMidpointDefect]

/-- Every nonnegative vertical displacement produces an inverse midpoint
offset in `[0, 1 / 2]`.  No upper bound on `δ` is needed because `fabiusInv`
is totalized by clamping above one. -/
theorem fabiusInvMidpointOffset_mem_Icc
    (F : BoundedFabius) (hF : IsFabius F) {δ : ℝ} (hδ0 : 0 ≤ δ) :
    fabiusInvMidpointOffset F hF δ ∈ Icc (0 : ℝ) (1 / 2) := by
  constructor
  · have hmono := monotone_fabiusInv F hF
      (show (1 / 2 : ℝ) ≤ 1 / 2 + δ by linarith)
    rw [fabiusInv_half F hF] at hmono
    change 0 ≤ fabiusInv F hF (1 / 2 + δ) - 1 / 2
    linarith
  · change fabiusInv F hF (1 / 2 + δ) - 1 / 2 ≤ 1 / 2
    linarith [fabiusInv_le_one F hF (1 / 2 + δ)]

/-- **Exact inverse midpoint equation.**  On the closed positive half-cell,
the vertical displacement is `2h - F(h)`, where `h` is the inverse midpoint
offset. -/
theorem fabiusInvMidpointOffset_equation
    (F : BoundedFabius) (hF : IsFabius F) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2) :
    δ = 2 * fabiusInvMidpointOffset F hF δ -
      fabiusReal F (fabiusInvMidpointOffset F hF δ) := by
  have hh := fabiusInvMidpointOffset_mem_Icc F hF hδ0
  have hy : (1 / 2 : ℝ) + δ ∈ Icc (0 : ℝ) 1 := by
    constructor <;> linarith
  have hforward := fabiusReal_fabiusInv F hF hy
  have hrecover :
      (1 / 2 : ℝ) + fabiusInvMidpointOffset F hF δ =
        fabiusInv F hF (1 / 2 + δ) := by
    dsimp only [fabiusInvMidpointOffset]
    ring
  rw [← hrecover,
    fabiusReal_midpoint_add_eq F hF hh.1 hh.2] at hforward
  linarith

/-- Fixed-point form of the exact inverse midpoint equation:
`h = δ / 2 + F(h) / 2`. -/
theorem fabiusInvMidpointOffset_fixedPoint
    (F : BoundedFabius) (hF : IsFabius F) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2) :
    fabiusInvMidpointOffset F hF δ = δ / 2 +
      fabiusReal F (fabiusInvMidpointOffset F hF δ) / 2 := by
  linarith [fabiusInvMidpointOffset_equation
    F hF hδ0 hδhalf]

/-- The inverse midpoint defect is exactly one half of the endpoint Fabius
value sampled at the inverse offset. -/
theorem fabiusInvMidpointDefect_eq_half_fabiusReal
    (F : BoundedFabius) (hF : IsFabius F) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2) :
    fabiusInvMidpointDefect F hF δ =
      fabiusReal F (fabiusInvMidpointOffset F hF δ) / 2 := by
  simp only [fabiusInvMidpointDefect]
  linarith [fabiusInvMidpointOffset_fixedPoint F hF hδ0 hδhalf]

/-- **Exact inverse-defect fixed point.**  On `0 ≤ δ ≤ 1 / 2`,

`E(δ) = F(δ / 2 + E(δ)) / 2`.

This is an identity, not an asymptotic approximation. -/
theorem fabiusInvMidpointDefect_fixedPoint
    (F : BoundedFabius) (hF : IsFabius F) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2) :
    fabiusInvMidpointDefect F hF δ =
      fabiusReal F (δ / 2 + fabiusInvMidpointDefect F hF δ) / 2 := by
  have harg :
      δ / 2 + fabiusInvMidpointDefect F hF δ =
        fabiusInvMidpointOffset F hF δ := by
    simp only [fabiusInvMidpointDefect]
    ring
  rw [harg]
  exact fabiusInvMidpointDefect_eq_half_fabiusReal
    F hF hδ0 hδhalf

/-- The exact positive inverse defect lies in `[0, 1 / 4]` throughout the
closed half-cell. -/
theorem fabiusInvMidpointDefect_mem_Icc
    (F : BoundedFabius) (hF : IsFabius F) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2) :
    fabiusInvMidpointDefect F hF δ ∈ Icc (0 : ℝ) (1 / 4) := by
  have hh := fabiusInvMidpointOffset_mem_Icc F hF hδ0
  have hnonneg := fabiusReal_nonneg F (fabiusInvMidpointOffset F hF δ)
  have hle := fabius_monotone F hF hh.2
  rw [fabius_half F hF] at hle
  rw [fabiusInvMidpointDefect_eq_half_fabiusReal F hF hδ0 hδhalf]
  constructor <;> linarith

/-- The inverse midpoint offset is globally odd, including the clamped tails
of the totalized inverse. -/
theorem fabiusInvMidpointOffset_neg
    (F : BoundedFabius) (hF : IsFabius F) (δ : ℝ) :
    fabiusInvMidpointOffset F hF (-δ) =
      -fabiusInvMidpointOffset F hF δ := by
  unfold fabiusInvMidpointOffset
  rw [show (1 / 2 : ℝ) + -δ = 1 - (1 / 2 + δ) by ring,
    fabiusInv_one_sub F hF (1 / 2 + δ)]
  ring

/-- The inverse midpoint defect is globally odd. -/
theorem fabiusInvMidpointDefect_neg
    (F : BoundedFabius) (hF : IsFabius F) (δ : ℝ) :
    fabiusInvMidpointDefect F hF (-δ) =
      -fabiusInvMidpointDefect F hF δ := by
  simp only [fabiusInvMidpointDefect, fabiusInvMidpointOffset_neg]
  ring

end

end Fabius
