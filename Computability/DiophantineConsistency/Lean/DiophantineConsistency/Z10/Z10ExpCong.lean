import DiophantineConsistency.Z10.Z10Size
import DiophantineConsistency.Z10.Z10Carrier
import DiophantineConsistency.ModelExponentialCongruence
import DiophantineConsistency.ModelRatioBounds

/-! # Ten-integer package 106: the exponential congruence, `W = 2^(2X+1)`

Soundness step S12 of the route. At a zero, the carrier divisibility
`S ∣ T` (`Z10Carrier.S_dvd_T`) with `S = 2A - 5` and
`T = 3 W C - 2 (W² - 1)` pins `W` to the power of two `2^(2X+1)`.

In the positive lane (`ModelRatio.ratio_power_of_congruence`) `A/2 = a + 2`,
`S = 4a + 3`, and Jones's congruence
`3 · 2ᵗ · ψ(t) ≡ 2 · (4ᵗ - 1) (mod 4a + 3)` is
`ModelExponentialCongruence.pow_congruence`. Here both `A` and `W` are signed:

* If `A/2 = -(a + 2)` then `S = -(4a + 13)`. Modulo `4a + 13` the Pell
  characteristic roots are `-2` and `-1/2`, so
  `x_t ≡ (-2)ᵗ + (a + 4) y_t`, and for odd `t` the same expression
  `3 · 2ᵗ · ψ(t) - 2 · (4ᵗ - 1)` is divisible by `4a + 13`
  (`odd_congruence`). The projection is proved for even indices by
  `𝚺₁` induction with one natural quotient on each side
  (`neg_projection`), since the sign of the quotient alternates.
* `signed_unique`: for a modulus `m ≥ 4a + 3` dividing both expressions,
  `m ∣ 2 (W - E)(E W + 1)`; with `|W|³, E³ < a + 2` the right side is
  smaller than `m` in absolute value for either sign of `W`, so it
  vanishes, and `W = -|W|` would make it positive. Hence `W = E`.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.Z10ExpCong
open Nine121 Nine121.N105Layout Z10Regs Z10Bootstrap Z10Squares Z10Guard Z10Index Z10KIndex
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing ZRowsCoprimeSquares ArithmeticPellRecurrence

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## The projection modulo `4a + 13` -/

/-- One Pell step from the even-type projection to the odd-type one. -/
theorem step_even (a t z1 z2 : V)
    (h : xcoord t a + (4 * a + 13) * z1 =
      Exp.exp t + (a + 4) * ycoord t a + (4 * a + 13) * z2) :
    xcoord (t + 1) a + Exp.exp (t + 1) + (4 * a + 13) * (ycoord t a + 2 * z2) =
      (a + 4) * ycoord (t + 1) a + (4 * a + 13) * (2 * z1) := by
  rw [x_succ, y_succ, exp_succ]
  unfold delta
  apply ι_injective (V := V)
  have h' := congrArg (ι (V := V)) h
  simp only [map_add, map_mul, map_one, map_ofNat] at h' ⊢
  linear_combination (-2 : DiffRing V) * h'

/-- One Pell step from the odd-type projection to the even-type one. -/
theorem step_odd (a t u1 u2 : V)
    (h : xcoord t a + Exp.exp t + (4 * a + 13) * u1 =
      (a + 4) * ycoord t a + (4 * a + 13) * u2) :
    xcoord (t + 1) a + (4 * a + 13) * (2 * u2 + ycoord t a) =
      Exp.exp (t + 1) + (a + 4) * ycoord (t + 1) a + (4 * a + 13) * (2 * u1) := by
  rw [x_succ, y_succ, exp_succ]
  unfold delta
  apply ι_injective (V := V)
  have h' := congrArg (ι (V := V)) h
  simp only [map_add, map_mul, map_one, map_ofNat] at h' ⊢
  linear_combination (-2 : DiffRing V) * h'

/-- `x_{2j} ≡ 4ʲ + (a + 4) y_{2j} (mod 4a + 13)`, with a natural quotient on
each side. -/
theorem neg_projection (a j : V) :
    ∃ z1 z2 : V, xcoord (2 * j) a + (4 * a + 13) * z1 =
      Exp.exp (2 * j) + (a + 4) * ycoord (2 * j) a + (4 * a + 13) * z2 := by
  induction j using ISigma1.sigma1_succ_induction
  · definability
  case zero => exact ⟨0, 0, by simp⟩
  case succ j ih =>
    obtain ⟨z1, z2, h⟩ := ih
    have h1 := step_even a (2 * j) z1 z2 h
    have h2 := step_odd a (2 * j + 1) _ _ h1
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring]
    exact ⟨_, _, h2⟩

/-- Jones's base-two congruence at an odd index, modulo `4a + 13`. -/
theorem odd_congruence (a j : V) :
    (4 * ι a + 13 : DiffRing V) ∣
      3 * ι (Exp.exp (2 * j + 1)) * ι (ycoord (2 * j + 1) a) -
        2 * (ι (Exp.exp (2 * j + 1)) ^ 2 - 1) := by
  obtain ⟨z1, z2, h⟩ := neg_projection a j
  have h1 := step_even a (2 * j) z1 z2 h
  have hn := ArithmeticPellRecurrence.norm (2 * j + 1) a
  unfold delta at hn
  have hx : ι (xcoord (2 * j + 1) a) =
      (ι a + 4) * ι (ycoord (2 * j + 1) a) - ι (Exp.exp (2 * j + 1)) +
        (4 * ι a + 13) * (2 * ι z1 - (ι (ycoord (2 * j) a) + 2 * ι z2)) := by
    have h' := congrArg (ι (V := V)) h1
    simp only [map_add, map_mul, map_ofNat] at h'
    linear_combination h'
  have hnorm : ι (xcoord (2 * j + 1) a) * ι (xcoord (2 * j + 1) a) =
      1 + (ι a + 1) * (ι a + 3) * ι (ycoord (2 * j + 1) a) * ι (ycoord (2 * j + 1) a) := by
    have := congrArg (ι (V := V)) hn
    simpa only [map_add, map_mul, map_one, map_ofNat] using this
  set E := ι (Exp.exp (2 * j + 1))
  set y := ι (ycoord (2 * j + 1) a)
  set A := ι a
  set Z := 2 * ι z1 - (ι (ycoord (2 * j) a) + 2 * ι z2)
  refine ⟨2 * y ^ 2 - E * y + 2 * Z * (2 * ((A + 4) * y - E) + (4 * A + 13) * Z), ?_⟩
  rw [hx] at hnorm
  linear_combination (-2 : DiffRing V) * hnorm

/-! ## Uniqueness for a signed `W` -/

/-- A modulus `m ≥ 4a + 3` dividing the congruence expression at a signed `W`
and at a natural `E ≥ 2`, both with cubes below `a + 2`, forces `W = E`. -/
theorem signed_unique (a Wn E : V) (m W Cc : DiffRing V)
    (hm : 4 * ι a + 3 ≤ m) (hWn : 0 < Wn) (hW : |W| = ι Wn) (hE2 : 2 ≤ E)
    (hW3 : Wn * Wn * Wn < a + 2) (hE3 : E * E * E < a + 2)
    (h1 : m ∣ 3 * W * Cc - 2 * (W * W - 1))
    (h2 : m ∣ 3 * ι E * Cc - 2 * (ι E ^ 2 - 1)) : W = ι E := by
  have ha0 : (0 : DiffRing V) ≤ ι a := ι_nonneg a
  have hpos : 0 < m := by linarith
  have he2 : (2 : DiffRing V) ≤ ι E := by
    have := (ι_le_ι (V := V)).mpr hE2
    simpa only [map_ofNat] using this
  have hw1 : (1 : DiffRing V) ≤ ι Wn := by
    have := (ι_le_ι (V := V)).mpr (pos_iff_one_le.mp hWn)
    simpa only [map_one] using this
  have hw3 : ι Wn * ι Wn * ι Wn + 1 ≤ ι a + 2 := by
    have := (ι_le_ι (V := V)).mpr (lt_iff_succ_le.mp hW3)
    simpa only [map_add, map_mul, map_one, map_ofNat] using this
  have he3 : ι E * ι E * ι E + 1 ≤ ι a + 2 := by
    have := (ι_le_ι (V := V)).mpr (lt_iff_succ_le.mp hE3)
    simpa only [map_add, map_mul, map_one, map_ofNat] using this
  have he0 : (0 : DiffRing V) ≤ ι E := by linarith
  have hw0 : (0 : DiffRing V) ≤ ι Wn := by linarith
  have key : 2 * (W - ι E) * (ι E * W + 1) =
      W * (3 * ι E * Cc - 2 * (ι E ^ 2 - 1)) - ι E * (3 * W * Cc - 2 * (W * W - 1)) := by
    ring
  have hd : m ∣ 2 * (W - ι E) * (ι E * W + 1) := by
    rw [key]
    exact dvd_sub (dvd_mul_of_dvd_right h2 _) (dvd_mul_of_dvd_right h1 _)
  rcases eq_or_eq_neg_abs W with hWs | hWs <;> rw [hW] at hWs
  · subst hWs
    have hzero : 2 * (ι Wn - ι E) * (ι E * ι Wn + 1) = 0 := by
      rcases le_total (ι Wn) (ι E) with h | h
      · have hb1 : (ι E - ι Wn) * (ι E * ι Wn + 1) ≤ (ι E - 1) * (ι E * ι E + 1) :=
          mul_le_mul (by linarith) (by linarith [mul_le_mul_of_nonneg_left h he0])
            (by linarith [_root_.mul_nonneg he0 hw0]) (by linarith)
        have hb0 : 0 ≤ (ι E - ι Wn) * (ι E * ι Wn + 1) :=
          _root_.mul_nonneg (by linarith) (by linarith [_root_.mul_nonneg he0 hw0])
        have hb : ι E ≤ ι E * ι E := le_mul_of_one_le_left he0 (by linarith)
        exact ModelRatio.eq_zero_of_dvd_small hpos hd (by linarith) (by linarith)
      · have hb1 : (ι Wn - ι E) * (ι E * ι Wn + 1) ≤ (ι Wn - 1) * (ι Wn * ι Wn + 1) :=
          mul_le_mul (by linarith) (by linarith [mul_le_mul_of_nonneg_right h hw0])
            (by linarith [_root_.mul_nonneg he0 hw0]) (by linarith)
        have hb0 : 0 ≤ (ι Wn - ι E) * (ι E * ι Wn + 1) :=
          _root_.mul_nonneg (by linarith) (by linarith [_root_.mul_nonneg he0 hw0])
        have hb : ι Wn ≤ ι Wn * ι Wn := le_mul_of_one_le_left hw0 hw1
        exact ModelRatio.eq_zero_of_dvd_small hpos hd (by linarith) (by linarith)
    have h3 : (ι Wn - ι E) * (ι E * ι Wn + 1) = 0 := by linarith
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact sub_eq_zero.mp h4
    · exfalso
      linarith [_root_.mul_nonneg he0 hw0]
  · subst hWs
    exfalso
    have hew : (2 : DiffRing V) * 1 ≤ ι E * ι Wn := mul_le_mul he2 hw1 (by norm_num) he0
    have hp : 0 < (ι Wn + ι E) * (ι E * ι Wn - 1) :=
      _root_.mul_pos (by linarith) (by linarith)
    have hzero : 2 * (-ι Wn - ι E) * (ι E * -ι Wn + 1) = 0 := by
      rcases le_total (ι Wn) (ι E) with h | h
      · have hb1 : (ι Wn + ι E) * (ι E * ι Wn - 1) ≤ (2 * ι E) * (ι E * ι E - 1) :=
          mul_le_mul (by linarith) (by linarith [mul_le_mul_of_nonneg_left h he0])
            (by linarith) (by linarith)
        exact ModelRatio.eq_zero_of_dvd_small hpos hd (by linarith) (by linarith)
      · have hb1 : (ι Wn + ι E) * (ι E * ι Wn - 1) ≤ (2 * ι Wn) * (ι Wn * ι Wn - 1) :=
          mul_le_mul (by linarith) (by linarith [mul_le_mul_of_nonneg_right h hw0])
            (by linarith) (by linarith)
        exact ModelRatio.eq_zero_of_dvd_small hpos hd (by linarith) (by linarith)
    linarith

/-! ## The register `W` -/

section Regs
variable (p : Fin 4 → DiffRing V) (x : Fin 10 → DiffRing V)
local notation "𝓡" => regs p x

/-- At a zero, `W = 2^(2X+1)`; in particular `W > 0`. -/
theorem W_eq (hz : value p x = 0) (Xn : V) (hX : (𝓡).X = ι Xn) (hX3 : 3 ≤ Xn) :
    (𝓡).W = ι (Exp.exp (2 * Xn + 1)) := by
  obtain ⟨a, pp, Wn, hA, -, -, hC, -, hW, hWn, hW3, hE3⟩ :=
    Z10Size.sizes p x hz Xn hX hX3
  have hST := Z10Carrier.S_dvd_T p x hz
  rw [T_def p x, hC] at hST
  have hE2 : (2 : V) ≤ Exp.exp (2 * Xn + 1) := by
    rw [exp_succ]
    exact le_mul_of_one_le_right (by simp) (one_le_exp _)
  have ha0 : (0 : DiffRing V) ≤ ι a := ι_nonneg a
  rcases eq_or_eq_neg_abs ((𝓡).halfA) with h | h <;> rw [hA] at h
  · have hS : (𝓡).S = 4 * ι a + 3 := by
      rw [S_def p x, A_def p x, h]
      simp only [map_add, map_ofNat]
      ring
    rw [hS] at hST
    exact signed_unique a Wn _ (4 * ι a + 3) _ _ le_rfl hWn hW hE2 hW3 hE3 hST
      (ModelExponentialCongruence.pow_congruence a (2 * Xn + 1))
  · have hS : (𝓡).S = -(4 * ι a + 13) := by
      rw [S_def p x, A_def p x, h]
      simp only [map_add, map_ofNat]
      ring
    rw [hS] at hST
    exact signed_unique a Wn _ (4 * ι a + 13) _ _ (by linarith) hWn hW hE2 hW3 hE3
      (neg_dvd.mp hST) (odd_congruence a Xn)

/-- At a zero, `W` is positive. -/
theorem W_pos (hz : value p x = 0) (Xn : V) (hX : (𝓡).X = ι Xn) (hX3 : 3 ≤ Xn) :
    0 < (𝓡).W := by
  rw [W_eq p x hz Xn hX hX3]
  have h := (ι_lt_ι (V := V)).mpr
    (lt_of_lt_of_le (by norm_num : (0 : V) < 1) (one_le_exp (2 * Xn + 1)))
  rwa [map_zero] at h

end Regs

#print axioms odd_congruence
#print axioms W_eq

end DiophantineConsistency.Z10ExpCong
