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
reflection symmetry.

The fixed-point layer already squeezes the defect by the Fabius function
itself: `δ = 2h - F(h) ≥ h` since `F(h) ≤ h` on `[0, 1/2]`, so
`0 ≤ E(δ) = F(h)/2 ≤ F(δ)/2`, and `E` inherits the **all-orders flatness**
of `F` at `0` (`fabiusInvMidpointDefect_isLittleO_pow`, two-sided by
oddness).  This file does not infer an asymptotic equivalence, a
logarithmic expansion, or a Lambert--W transfer from the fixed-point
equation.
-/

set_option autoImplicit false

open Set Filter Asymptotics

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

/-! ## All-orders flatness of the defect -/

/-- `F(x) ≤ x` on the closed first half `[0, 1/2]`: the strict interior
inequality `fabiusReal_lt_self_of_mem_Ioo_zero_half` plus the two
endpoint values `F(0) = 0`, `F(1/2) = 1/2`. -/
theorem fabiusReal_le_self_of_mem_Icc_zero_half
    (F : BoundedFabius) (hF : IsFabius F) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) (1 / 2)) :
    fabiusReal F x ≤ x := by
  rcases eq_or_lt_of_le hx.1 with h0 | h0
  · rw [← h0, hF.zero_of_nonpos 0 le_rfl]
  · rcases eq_or_lt_of_le hx.2 with h1 | h1
    · rw [h1, fabius_half F hF]
    · exact (fabiusReal_lt_self_of_mem_Ioo_zero_half F hF ⟨h0, h1⟩).le

/-- The inverse midpoint offset is at most the vertical displacement:
`h ≤ δ`, because `δ = 2h - F(h)` and `F(h) ≤ h`. -/
theorem fabiusInvMidpointOffset_le
    (F : BoundedFabius) (hF : IsFabius F) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2) :
    fabiusInvMidpointOffset F hF δ ≤ δ := by
  have hh := fabiusInvMidpointOffset_mem_Icc F hF hδ0
  have heq := fabiusInvMidpointOffset_equation F hF hδ0 hδhalf
  have hle := fabiusReal_le_self_of_mem_Icc_zero_half F hF hh
  linarith

/-- **The defect is squeezed by the Fabius function itself**:
`0 ≤ E(δ) ≤ F(δ)/2` on the closed half-cell. -/
theorem fabiusInvMidpointDefect_le_half_fabiusReal
    (F : BoundedFabius) (hF : IsFabius F) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2) :
    fabiusInvMidpointDefect F hF δ ≤ fabiusReal F δ / 2 := by
  rw [fabiusInvMidpointDefect_eq_half_fabiusReal F hF hδ0 hδhalf]
  have := fabius_monotone F hF (fabiusInvMidpointOffset_le F hF hδ0 hδhalf)
  linarith

/-- The two-sided squeeze, by oddness: `|E(δ)| ≤ F(|δ|)/2` for
`|δ| ≤ 1/2`. -/
theorem abs_fabiusInvMidpointDefect_le
    (F : BoundedFabius) (hF : IsFabius F) {δ : ℝ} (hδ : |δ| ≤ 1 / 2) :
    |fabiusInvMidpointDefect F hF δ| ≤ fabiusReal F |δ| / 2 := by
  rcases le_or_gt 0 δ with h0 | h0
  · rw [abs_of_nonneg h0] at hδ ⊢
    have hE := fabiusInvMidpointDefect_mem_Icc F hF h0 hδ
    rw [abs_of_nonneg hE.1]
    exact fabiusInvMidpointDefect_le_half_fabiusReal F hF h0 hδ
  · rw [abs_of_neg h0] at hδ ⊢
    have h0' : 0 ≤ -δ := by linarith
    have hE := fabiusInvMidpointDefect_mem_Icc F hF h0' hδ
    have hodd : fabiusInvMidpointDefect F hF δ =
        -fabiusInvMidpointDefect F hF (-δ) := by
      rw [← fabiusInvMidpointDefect_neg, neg_neg]
    rw [hodd, abs_neg, abs_of_nonneg hE.1]
    exact fabiusInvMidpointDefect_le_half_fabiusReal F hF h0' hδ

/-- **All-orders flatness of the inverse midpoint defect**: for every `n`,
`E(δ) = o(δⁿ)` as `δ → 0` (two-sided).  The defect is bounded by
`F(|δ|)/2`, and the Fabius function is flat to all orders at `0`. -/
theorem fabiusInvMidpointDefect_isLittleO_pow
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    fabiusInvMidpointDefect F hF =o[nhds 0] (fun δ : ℝ => δ ^ n) := by
  have habs : Tendsto (fun δ : ℝ => |δ|) (nhds (0 : ℝ)) (nhds (0 : ℝ)) := by
    have := continuous_abs.tendsto (0 : ℝ)
    simpa only [abs_zero] using this
  have hflat : (fun δ : ℝ => fabiusReal F |δ|) =o[nhds 0]
      (fun δ : ℝ => δ ^ n) := by
    have h := (fabiusReal_isLittleO_pow_at_zero F hF n).comp_tendsto habs
    have h' : (fun δ : ℝ => fabiusReal F |δ|) =o[nhds 0]
        (fun δ : ℝ => ‖δ ^ n‖) := by
      refine h.congr' (Filter.Eventually.of_forall fun _ => rfl)
        (Filter.Eventually.of_forall fun δ => ?_)
      simp only [Function.comp_apply, Real.norm_eq_abs, abs_pow]
    exact isLittleO_norm_right.mp h'
  refine (IsBigO.of_bound (1 / 2) ?_).trans_isLittleO hflat
  filter_upwards [Ioo_mem_nhds (show (-(1 / 2) : ℝ) < 0 by norm_num)
    (show (0 : ℝ) < 1 / 2 by norm_num)] with δ hδ
  have hδ' : |δ| ≤ 1 / 2 := (abs_lt.mpr ⟨hδ.1, hδ.2⟩).le
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (fabiusReal_nonneg F _)]
  have := abs_fabiusInvMidpointDefect_le F hF hδ'
  linarith

end

end Fabius
