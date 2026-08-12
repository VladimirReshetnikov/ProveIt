import Mathlib.Tactic.NormNum

/-!
# A rational supersolution certificate for Bui's polyomino recurrences

This file contains only the finite algebraic part of the upper bound for
Klarner's polyomino constant.  The profile coordinates and polynomial map are
ordered `c, d, e, f, g, h, p, q, r, s, t, u, v, w, x, y, z`, following the
seventeen generating-function inequalities in Bui's recurrence system.

At `ζ = 2000 / 9047`, the exact rational profile below is a componentwise
supersolution.  Thus the associated exponential base is `ζ⁻¹ = 9047 / 2000 =
4.5235`.  The connection between this finite certificate and the recurrence
sequences is proved separately.
-/

namespace LeanProofs.KlarnerConstant

/-- The seventeen coordinates in Bui's generating-function recurrence system. -/
structure Profile where
  c : ℚ
  d : ℚ
  e : ℚ
  f : ℚ
  g : ℚ
  h : ℚ
  p : ℚ
  q : ℚ
  r : ℚ
  s : ℚ
  t : ℚ
  u : ℚ
  v : ℚ
  w : ℚ
  x : ℚ
  y : ℚ
  z : ℚ
  deriving DecidableEq, Repr

/-- Componentwise order on the seventeen-coordinate profiles. -/
def Profile.ComponentwiseLE (a b : Profile) : Prop :=
  a.c ≤ b.c ∧
  a.d ≤ b.d ∧
  a.e ≤ b.e ∧
  a.f ≤ b.f ∧
  a.g ≤ b.g ∧
  a.h ≤ b.h ∧
  a.p ≤ b.p ∧
  a.q ≤ b.q ∧
  a.r ≤ b.r ∧
  a.s ≤ b.s ∧
  a.t ≤ b.t ∧
  a.u ≤ b.u ∧
  a.v ≤ b.v ∧
  a.w ≤ b.w ∧
  a.x ≤ b.x ∧
  a.y ≤ b.y ∧
  a.z ≤ b.z

/-- Every coordinate of a profile is nonnegative. -/
def Profile.Nonnegative (a : Profile) : Prop :=
  0 ≤ a.c ∧
  0 ≤ a.d ∧
  0 ≤ a.e ∧
  0 ≤ a.f ∧
  0 ≤ a.g ∧
  0 ≤ a.h ∧
  0 ≤ a.p ∧
  0 ≤ a.q ∧
  0 ≤ a.r ∧
  0 ≤ a.s ∧
  0 ≤ a.t ∧
  0 ≤ a.u ∧
  0 ≤ a.v ∧
  0 ≤ a.w ∧
  0 ≤ a.x ∧
  0 ≤ a.y ∧
  0 ≤ a.z

/--
The polynomial map induced by Bui's seventeen generating-function recurrences.

For example, the first and seventh coordinates encode
`C = ζ + ζ E` and `P = E H + Q D + X R + V Y + U Y Z`.
-/
def buiMap (ζ : ℚ) (a : Profile) : Profile where
  c := ζ + ζ * a.e
  d := ζ + ζ * a.g
  e := ζ + ζ * a.f
  f := a.g + a.p
  g := a.e + a.q
  h := a.d + a.s
  p := a.e * a.h + a.q * a.d + a.x * a.r + a.v * a.y + a.u * a.y * a.z
  q := ζ * a.g + ζ * a.g * a.e + ζ ^ 2 * (a.u + a.t * a.g + a.r * a.u)
  r := a.y + a.w
  s := ζ * a.g + ζ * a.e ^ 2 + ζ ^ 2 * a.t + ζ ^ 2 * a.x * a.g +
    ζ ^ 2 * a.y * a.u
  t := a.x + a.v
  u := a.d * a.h + a.s * a.d + a.y * a.r + a.w * a.y + a.u * a.z ^ 2
  v := ζ * a.s + ζ ^ 2 * (a.g ^ 2 + a.t * a.e + a.r * a.t)
  w := ζ * a.s + ζ ^ 2 * (a.e * a.g + a.x * a.e + a.y * a.t)
  x := ζ * a.d + ζ ^ 2 * (a.g + a.u)
  y := ζ * a.c + ζ ^ 2 * (a.g + a.t)
  z := ζ * a.c + ζ ^ 2 * (a.e + a.x)

/-- A profile is a supersolution when Bui's polynomial map lies below it. -/
def IsSupersolution (ζ : ℚ) (a : Profile) : Prop :=
  (buiMap ζ a).ComponentwiseLE a

/-- The reciprocal of the claimed exponential upper bound `4.5235`. -/
def certificateZeta : ℚ := 2000 / 9047

/--
An exact rational supersolution at `ζ = 2000 / 9047`.

All coordinates have the common denominator `10^7`.
-/
def certificate : Profile where
  c := 3_482_045 / 10_000_000
  d := 4_310_668 / 10_000_000
  e := 5_751_028 / 10_000_000
  f := 16_014_774 / 10_000_000
  g := 9_499_305 / 10_000_000
  h := 7_394_875 / 10_000_000
  p := 6_515_468 / 10_000_000
  q := 3_748_277 / 10_000_000
  r := 2_390_936 / 10_000_000
  s := 3_084_206 / 10_000_000
  t := 2_902_315 / 10_000_000
  u := 5_050_537 / 10_000_000
  v := 1_238_300 / 10_000_000
  w := 1_015_088 / 10_000_000
  x := 1_664_015 / 10_000_000
  y := 1_375_847 / 10_000_000
  z := 1_132_149 / 10_000_000

theorem certificateZeta_pos : 0 < certificateZeta := by
  norm_num [certificateZeta]

theorem certificate_nonnegative : certificate.Nonnegative := by
  norm_num [certificate, Profile.Nonnegative]

theorem certificate_g_lt_one : certificate.g < 1 := by
  norm_num [certificate]

/-- The `c`-coordinate certificate inequality. -/
theorem certificate_c_inequality :
    (buiMap certificateZeta certificate).c ≤ certificate.c := by
  norm_num [buiMap, certificateZeta, certificate]

/-- The `d`-coordinate certificate inequality. -/
theorem certificate_d_inequality :
    (buiMap certificateZeta certificate).d ≤ certificate.d := by
  norm_num [buiMap, certificateZeta, certificate]

/-- The `e`-coordinate certificate inequality. -/
theorem certificate_e_inequality :
    (buiMap certificateZeta certificate).e ≤ certificate.e := by
  norm_num [buiMap, certificateZeta, certificate]

/-- The `f`-coordinate certificate inequality. -/
theorem certificate_f_inequality :
    (buiMap certificateZeta certificate).f ≤ certificate.f := by
  norm_num [buiMap, certificateZeta, certificate]

/-- The `g`-coordinate certificate inequality. -/
theorem certificate_g_inequality :
    (buiMap certificateZeta certificate).g ≤ certificate.g := by
  norm_num [buiMap, certificateZeta, certificate]

/-- The `h`-coordinate certificate inequality. -/
theorem certificate_h_inequality :
    (buiMap certificateZeta certificate).h ≤ certificate.h := by
  norm_num [buiMap, certificateZeta, certificate]

/-- The `p`-coordinate certificate inequality. -/
theorem certificate_p_inequality :
    (buiMap certificateZeta certificate).p ≤ certificate.p := by
  norm_num [buiMap, certificateZeta, certificate]

/-- The `q`-coordinate certificate inequality. -/
theorem certificate_q_inequality :
    (buiMap certificateZeta certificate).q ≤ certificate.q := by
  norm_num [buiMap, certificateZeta, certificate]

/-- The `r`-coordinate certificate inequality. -/
theorem certificate_r_inequality :
    (buiMap certificateZeta certificate).r ≤ certificate.r := by
  norm_num [buiMap, certificateZeta, certificate]

/-- The `s`-coordinate certificate inequality. -/
theorem certificate_s_inequality :
    (buiMap certificateZeta certificate).s ≤ certificate.s := by
  norm_num [buiMap, certificateZeta, certificate]

/-- The `t`-coordinate certificate inequality. -/
theorem certificate_t_inequality :
    (buiMap certificateZeta certificate).t ≤ certificate.t := by
  norm_num [buiMap, certificateZeta, certificate]

/-- The `u`-coordinate certificate inequality. -/
theorem certificate_u_inequality :
    (buiMap certificateZeta certificate).u ≤ certificate.u := by
  norm_num [buiMap, certificateZeta, certificate]

/-- The `v`-coordinate certificate inequality. -/
theorem certificate_v_inequality :
    (buiMap certificateZeta certificate).v ≤ certificate.v := by
  norm_num [buiMap, certificateZeta, certificate]

/-- The `w`-coordinate certificate inequality. -/
theorem certificate_w_inequality :
    (buiMap certificateZeta certificate).w ≤ certificate.w := by
  norm_num [buiMap, certificateZeta, certificate]

/-- The `x`-coordinate certificate inequality. -/
theorem certificate_x_inequality :
    (buiMap certificateZeta certificate).x ≤ certificate.x := by
  norm_num [buiMap, certificateZeta, certificate]

/-- The `y`-coordinate certificate inequality. -/
theorem certificate_y_inequality :
    (buiMap certificateZeta certificate).y ≤ certificate.y := by
  norm_num [buiMap, certificateZeta, certificate]

/-- The `z`-coordinate certificate inequality. -/
theorem certificate_z_inequality :
    (buiMap certificateZeta certificate).z ≤ certificate.z := by
  norm_num [buiMap, certificateZeta, certificate]

/-- The kernel-checked conjunction of all seventeen certificate inequalities. -/
theorem certificate_isSupersolution : IsSupersolution certificateZeta certificate := by
  exact ⟨certificate_c_inequality, certificate_d_inequality, certificate_e_inequality,
    certificate_f_inequality, certificate_g_inequality, certificate_h_inequality,
    certificate_p_inequality, certificate_q_inequality, certificate_r_inequality,
    certificate_s_inequality, certificate_t_inequality, certificate_u_inequality,
    certificate_v_inequality, certificate_w_inequality, certificate_x_inequality,
    certificate_y_inequality, certificate_z_inequality⟩

end LeanProofs.KlarnerConstant
