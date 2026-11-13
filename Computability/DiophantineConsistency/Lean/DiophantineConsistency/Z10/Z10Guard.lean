import DiophantineConsistency.Z10.Z10Squares

/-! # The short approximation guard of the ten-integer forms

Package 106, integer lane (step S6 of the route, and the algebra of step C6). `𝓡 = Z10Regs.regs p x`
at a signed assignment in the ring of differences of a model of `𝗜𝚺₁`; no port fact is used.

The guard discriminant is `Delta = g (cap − g) K² − cap² e²` with `e = C − K L`, and
`Z10Squares.Delta_pos` makes it positive at a zero.

* `radix_pos`, `threshold_pos`, `Bc_pos`, `capc_pos`, `Yc_pos`: the scales are positive at a
  positive `b`; `cap_pos`, `Y_pos`: hence `cap > 0` and `Y > 0` at a zero.
* `short_guard`: for `cap > 0`, `Delta > 0` forces `K ≠ 0`, `0 < g < cap` and, through
  `4 g (cap − g) = cap² − (cap − 2g)² ≤ cap²`, the approximation `4 e² < K²`.
* `guard`: these four facts at a zero; `two_e_lt`: `2 |C − K L| < |K|`.
* `l_ne`: `l = x 4 ≠ 0` at a zero (otherwise `Phalf = 0` and `Q = 1 − K² ≤ 0`); `abs_L_ge`:
  `|Y| ≤ |L|`.
* `C_interval`: `|K| (2 |L| − 1) < 2 |C| < |K| (2 |L| + 1)`; `one_lt_abs_C`: `|C| > 1` as soon as
  `|L| ≥ 2`.
* `guard_complete` (for the completeness direction): if `0 < g < cap`, `K ≠ 0`,
  `16 g² e² ≤ K²` and `cap² ≤ g³`, then `Delta > 0`, because `16 g² Delta ≥ 15 g³ K²`. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.Z10Guard
open Nine121 Nine121.N105Layout Z10Regs Z10Bootstrap Z10Squares
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing
open P138Bootstrap (one_le_of_pos' one_le_abs)

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## The scales are positive -/

theorem radix_pos : (0 : DiffRing V) < ((radix : ℤ) : DiffRing V) := by
  rw [radix_eq, Int.cast_pow]
  exact pow_pos (by norm_num) _

theorem threshold_pos : (0 : DiffRing V) < ((threshold : ℤ) : DiffRing V) := by
  unfold threshold
  rw [Int.cast_pow]
  exact pow_pos (by norm_num) _

theorem Bc_pos {b : DiffRing V} (hb : 0 < b) : 0 < Bc b := by
  unfold Bc; exact mul_pos radix_pos (mul_pos hb hb)

theorem capc_pos {b : DiffRing V} (hb : 0 < b) : 0 < cap b := by
  unfold cap; exact mul_pos hb (pow_pos (Bc_pos hb) _)

theorem Yc_pos {b : DiffRing V} (hb : 0 < b) : 0 < Yc b := by
  unfold Yc; exact mul_pos hb (mul_pos threshold_pos (pow_pos (Bc_pos hb) _))

/-! ## The guard over plain variables -/

theorem mul_self_pos' {a : DiffRing V} (h : a ≠ 0) : 0 < a * a :=
  lt_of_le_of_ne (mul_self_nonneg a) (Ne.symm (mul_ne_zero h h))

/-- **The short guard.** With `c > 0`, positivity of `g (c − g) K² − c² e²` forces `K ≠ 0`,
`0 < g < c` and `4 e² < K²`. -/
theorem short_guard {g c K e : DiffRing V} (hc : 0 < c)
    (hD : 0 < g * (c - g) * (K * K) - c * c * (e * e)) :
    K ≠ 0 ∧ 0 < g ∧ g < c ∧ 4 * (e * e) < K * K := by
  have he : 0 ≤ c * c * (e * e) := mul_nonneg (mul_self_nonneg c) (mul_self_nonneg e)
  have hprod : 0 < g * (c - g) * (K * K) := by linarith
  have hK : K ≠ 0 := by
    intro h0
    have : g * (c - g) * (K * K) = 0 := by rw [h0]; ring
    linarith
  have hKK : 0 < K * K := mul_self_pos' hK
  have hprod' : 0 < K * K * (g * (c - g)) := by
    have e1 : K * K * (g * (c - g)) = g * (c - g) * (K * K) := by ring
    rw [e1]; exact hprod
  have hg : 0 < g * (c - g) := pos_of_mul_pos_right hprod' hKK.le
  have hg0 : 0 < g := by
    by_contra hn
    have h1 : 0 ≤ -g := by linarith [not_lt.mp hn]
    have h2 : 0 ≤ c - g := by linarith
    have h3 := mul_nonneg h1 h2
    have e1 : -g * (c - g) = -(g * (c - g)) := by ring
    rw [e1] at h3
    linarith
  have hgc : g < c := by
    by_contra hn
    have h2 : 0 ≤ g - c := by linarith [not_lt.mp hn]
    have h3 := mul_nonneg hg0.le h2
    have e1 : g * (g - c) = -(g * (c - g)) := by ring
    rw [e1] at h3
    linarith
  have h5 : 4 * (g * (c - g)) ≤ c * c := by
    have h := mul_self_nonneg (c - 2 * g)
    have e1 : (c - 2 * g) * (c - 2 * g) = c * c - 4 * (g * (c - g)) := by ring
    rw [e1] at h
    linarith
  have h6 : 4 * (g * (c - g)) * (K * K) ≤ c * c * (K * K) :=
    mul_le_mul_of_nonneg_right h5 hKK.le
  have h4 : c * c * (4 * (e * e)) < c * c * (K * K) := by
    have e1 : c * c * (4 * (e * e)) = 4 * (c * c * (e * e)) := by ring
    have e2 : 4 * (g * (c - g)) * (K * K) = 4 * (g * (c - g) * (K * K)) := by ring
    rw [e1]; rw [e2] at h6
    linarith
  refine ⟨hK, hg0, hgc, ?_⟩
  by_contra hn
  have := mul_le_mul_of_nonneg_left (le_of_not_gt hn) (mul_self_nonneg c)
  linarith

/-- `4 e² < K²` as `2 |e| < |K|`. -/
theorem two_abs_lt {e K : DiffRing V} (h : 4 * (e * e) < K * K) : 2 * |e| < |K| := by
  have h' : (2 * e) ^ 2 < K ^ 2 := by
    have e1 : (2 * e) ^ 2 = 4 * (e * e) := by ring
    have e2 : K ^ 2 = K * K := by ring
    rw [e1, e2]; exact h
  have := _root_.sq_lt_sq.mp h'
  rw [abs_mul, abs_two] at this
  exact this

/-- **The interval of an approximated product**: `C = K L + e` with `2 |e| < |K|`. -/
theorem interval_of_approx {C K L e : DiffRing V} (hC : C = K * L + e) (h : 2 * |e| < |K|) :
    |K| * (2 * |L| - 1) < 2 * |C| ∧ 2 * |C| < |K| * (2 * |L| + 1) := by
  have hKL : |K * L| = |K| * |L| := abs_mul _ _
  have hup : |C| ≤ |K| * |L| + |e| := by
    rw [hC, ← hKL]; exact abs_add_le _ _
  have hlow : |K| * |L| ≤ |C| + |e| := by
    rw [← hKL]
    have : K * L = C - e := by rw [hC]; ring
    rw [this]
    exact abs_le.mpr ⟨by linarith [neg_abs_le C, le_abs_self e],
      by linarith [le_abs_self C, neg_abs_le e]⟩
  have e1 : |K| * (2 * |L| - 1) = 2 * (|K| * |L|) - |K| := by ring
  have e2 : |K| * (2 * |L| + 1) = 2 * (|K| * |L|) + |K| := by ring
  rw [e1, e2]
  constructor <;> linarith

/-- **The guard in the completeness direction.** `16 g² · (g (c − g) K² − c² e²) ≥ 15 g³ K²`. -/
theorem guard_complete {g c K e : DiffRing V} (hg : 0 < g) (hgc : g < c) (hK : K ≠ 0)
    (he : 16 * (g * g) * (e * e) ≤ K * K) (hc : c * c ≤ g * g * g) :
    0 < g * (c - g) * (K * K) - c * c * (e * e) := by
  have hKK : 0 < K * K := mul_self_pos' hK
  have h1 : 1 ≤ c - g := one_le_of_pos' (by linarith)
  have hgg : 0 < g * g := mul_pos hg hg
  have hpos : 0 < g * g * g * (K * K) := mul_pos (mul_pos hgg hg) hKK
  have hA : c * c * (16 * (g * g) * (e * e)) ≤ c * c * (K * K) :=
    mul_le_mul_of_nonneg_left he (mul_self_nonneg c)
  have hB : c * c * (K * K) ≤ g * g * g * (K * K) := mul_le_mul_of_nonneg_right hc hKK.le
  have hC : g * g * g * (K * K) * 1 ≤ g * g * g * (K * K) * (c - g) :=
    mul_le_mul_of_nonneg_left h1 hpos.le
  have h16 : 0 < 16 * (g * g) * (g * (c - g) * (K * K) - c * c * (e * e)) := by
    have e1 : 16 * (g * g) * (g * (c - g) * (K * K) - c * c * (e * e)) =
        16 * (g * g * g * (K * K) * (c - g)) - c * c * (16 * (g * g) * (e * e)) := by ring
    rw [e1]
    linarith
  exact pos_of_mul_pos_right h16 (by linarith)

/-! ## The guard at a zero -/

section Regs
variable (p : Fin 4 → DiffRing V) (x : Fin 10 → DiffRing V)
local notation "𝓡" => regs p x

theorem cap_pos (hz : value p x = 0) : 0 < (𝓡).cap := by
  rw [cap_def]; exact capc_pos (b_pos p x hz)

theorem Y_pos (hz : value p x = 0) : 0 < (𝓡).Y := by
  rw [Y_def]; exact Yc_pos (b_pos p x hz)

/-- **The short guard at a zero**: `K ≠ 0`, `0 < g < cap` and `4 (C − K L)² < K²`. -/
theorem guard (hz : value p x = 0) :
    (𝓡).K ≠ 0 ∧ 0 < (𝓡).g ∧ (𝓡).g < (𝓡).cap ∧
      4 * (((𝓡).C - (𝓡).K * (𝓡).L) * ((𝓡).C - (𝓡).K * (𝓡).L)) < (𝓡).K * (𝓡).K := by
  have hD := Delta_pos p x hz
  rw [Delta_def] at hD
  exact short_guard (cap_pos p x hz) hD

theorem two_e_lt (hz : value p x = 0) : 2 * |(𝓡).C - (𝓡).K * (𝓡).L| < |(𝓡).K| :=
  two_abs_lt (guard p x hz).2.2.2

/-- **The scale `l` is nonzero at a zero**: otherwise `Phalf = 0` and `Q = 1 − K² ≤ 0`. -/
theorem l_ne (hz : value p x = 0) : x 4 ≠ 0 := by
  intro h0
  have hK := (guard p x hz).1
  have hQ := Q_pos p x hz
  have hP : (𝓡).Phalf = 0 := by
    rw [Phalf_def, U_def, halfU_def, L_def, h0]; ring
  rw [Q_def, hP] at hQ
  have h1 : 1 ≤ (𝓡).K * (𝓡).K := one_le_of_pos' (mul_self_pos' hK)
  have e1 : ((0 : DiffRing V) * 0 - 1) * ((𝓡).K * (𝓡).K) + 1 = 1 - (𝓡).K * (𝓡).K := by ring
  rw [e1] at hQ
  linarith

theorem abs_L_ge (hz : value p x = 0) : |(𝓡).Y| ≤ |(𝓡).L| := by
  rw [L_def, abs_mul]
  have h1 := one_le_abs (l_ne p x hz)
  have h2 := mul_le_mul_of_nonneg_right h1 (abs_nonneg (𝓡).Y)
  rw [one_mul] at h2
  exact h2

/-- **The interval for `C`** (`|C/K − L| < 1/2`). -/
theorem C_interval (hz : value p x = 0) :
    |(𝓡).K| * (2 * |(𝓡).L| - 1) < 2 * |(𝓡).C| ∧
      2 * |(𝓡).C| < |(𝓡).K| * (2 * |(𝓡).L| + 1) :=
  interval_of_approx (e := (𝓡).C - (𝓡).K * (𝓡).L) (by ring) (two_e_lt p x hz)

theorem one_lt_abs_C (hz : value p x = 0) (hL : 2 ≤ |(𝓡).L|) : 1 < |(𝓡).C| := by
  have hK1 := one_le_abs (guard p x hz).1
  have h := (C_interval p x hz).1
  have h3 := mul_nonneg (sub_nonneg.mpr hK1) (sub_nonneg.mpr hL)
  have e1 : (|(𝓡).K| - 1) * (|(𝓡).L| - 2) = |(𝓡).K| * |(𝓡).L| - 2 * |(𝓡).K| - |(𝓡).L| + 2 := by
    ring
  have e2 : |(𝓡).K| * (2 * |(𝓡).L| - 1) = 2 * (|(𝓡).K| * |(𝓡).L|) - |(𝓡).K| := by ring
  rw [e1] at h3
  rw [e2] at h
  linarith

end Regs

#print axioms short_guard
#print axioms guard_complete
#print axioms guard
#print axioms l_ne
#print axioms C_interval
#print axioms one_lt_abs_C

end DiophantineConsistency.Z10Guard
