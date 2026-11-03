import DiophantineConsistency.TenPositiveTrace75
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.Ring.Abs

/-! # Signed transport and the recovery of `B ≥ 0`, `C > 0` (stage K7)

Package 163, `compact/PROOF.md` §§4–5, for chart `q3` and weight `L = V²`
(the 75/402 circuit). Every statement is about the registers
`TenPositiveTrace75.regs p v` in an arbitrary discrete ordered commutative
ring, so it applies verbatim in the ring of differences `DiffRing V` of every
model of `𝗜𝚺₁` (`hdisc` is `ModelDifferenceRing.one_le_of_pos`).

The inputs are the outputs of the root stages: `g, y > 0` with `|z| = g y`,
`Z = M z` and the auxiliary norm `Q V² − (Q − 1) y² = 1`, together with
elementary register sizes. With weight `V²` neither the main index nor
`p ≥ 5` is needed: `b = 0` is excluded by `Q > c²` alone.

This module imports neither Foundation nor Mathlib's matrices. -/
set_option autoImplicit false
namespace DiophantineConsistency.TenPositiveTransport
open TenPositiveTrace75

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
variable (p : Fin 4 → R) (v : Fin 10 → R)
local notation "𝓡" => regs p v

/-- `e < b`, since `b − e = c T − k + 1`. -/
theorem e_lt_b (hT : 1 ≤ v 4) (hc : 0 < (𝓡).c) (hck : (𝓡).k < (𝓡).c) :
    (𝓡).e < (𝓡).b := by
  rw [e_def, b_def]
  have : (𝓡).c ≤ (𝓡).c * v 4 := le_mul_of_one_le_right hc.le hT
  linarith

/-- `b ≠ 0`: otherwise `(Q − 1)(y² − c²) = c² − 1` lies strictly between `0` and `Q − 1`. -/
theorem b_ne_zero (hdisc : ∀ x : R, 0 < x → 1 ≤ x) {y : R}
    (hnorm : (𝓡).Q * (𝓡).V ^ 2 - ((𝓡).Q - 1) * y ^ 2 = 1)
    (hc : 2 ≤ (𝓡).c) (hQ : (𝓡).c ^ 2 < (𝓡).Q) : (𝓡).b ≠ 0 := by
  intro hb
  have hV : (𝓡).V = -(𝓡).c := by rw [V_def, hb]; ring
  rw [hV] at hnorm
  set Q := (𝓡).Q
  set c := (𝓡).c
  have hQ1 : 0 < Q - 1 := by nlinarith
  have key : (Q - 1) * (y ^ 2 - c ^ 2) = c ^ 2 - 1 := by linear_combination -hnorm
  have hpos : 0 < y ^ 2 - c ^ 2 := by
    by_contra hn
    push_neg at hn
    have : (Q - 1) * (y ^ 2 - c ^ 2) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hQ1.le hn
    nlinarith
  have h1 := hdisc _ hpos
  have : Q - 1 ≤ (Q - 1) * (y ^ 2 - c ^ 2) := le_mul_of_one_le_right hQ1.le h1
  nlinarith

/-- `f − c ≤ |V|` and `|b| < |V|`, once `b ≠ 0` and `f > 2c`. -/
theorem abs_V_bounds (hdisc : ∀ x : R, 0 < x → 1 ≤ x) (hb : (𝓡).b ≠ 0)
    (hc : 1 ≤ (𝓡).c) (hfc : 2 * (𝓡).c < (𝓡).f) :
    (𝓡).f - (𝓡).c ≤ |(𝓡).V| ∧ |(𝓡).b| < |(𝓡).V| := by
  have hb1 : 1 ≤ |(𝓡).b| := hdisc _ (abs_pos.mpr hb)
  have hf0 : 0 < (𝓡).f := by linarith
  have hfb : (𝓡).f * |(𝓡).b| - (𝓡).c ≤ |(𝓡).V| := by
    rw [V_def]
    have h1 : |(𝓡).f * (𝓡).b| - |(𝓡).c| ≤ |(𝓡).f * (𝓡).b - (𝓡).c| := abs_sub_abs_le_abs_sub _ _
    rw [abs_mul, abs_of_pos hf0, abs_of_pos (by linarith : (0 : R) < (𝓡).c)] at h1
    exact h1
  have hfb1 : (𝓡).f ≤ (𝓡).f * |(𝓡).b| := le_mul_of_one_le_right hf0.le hb1
  refine ⟨by linarith, ?_⟩
  have : ((𝓡).f - 1) * 1 ≤ ((𝓡).f - 1) * |(𝓡).b| :=
    mul_le_mul_of_nonneg_left hb1 (by linarith)
  nlinarith

/-- `2y < 3|V|` from the auxiliary norm with `Q ≥ 2`. -/
theorem two_y_lt {y : R} (hy : 0 < y) (hQ : 2 ≤ (𝓡).Q)
    (hnorm : (𝓡).Q * (𝓡).V ^ 2 - ((𝓡).Q - 1) * y ^ 2 = 1) : 2 * y < 3 * |(𝓡).V| := by
  set Q := (𝓡).Q
  have hV2 : |(𝓡).V| ^ 2 = (𝓡).V ^ 2 := sq_abs _
  have hlt : y ^ 2 < 2 * (𝓡).V ^ 2 := by nlinarith
  by_contra hn
  push_neg at hn
  have h0 : 0 ≤ 3 * |(𝓡).V| := by positivity
  nlinarith

/-- `3g < a` when `G = g²`, `Delta U² ≥ 18` and `E > 0`. -/
theorem three_g_lt_a (hdisc : ∀ x : R, 0 < x → 1 ≤ x) {g : R} (hg : 0 < g)
    (hG : (𝓡).Gn = g ^ 2) (hE : 0 < (𝓡).E) (hDU : 18 ≤ (𝓡).Delta * (𝓡).U ^ 2) :
    3 * g < (𝓡).a := by
  have ha : (𝓡).a = (𝓡).Delta * (𝓡).U ^ 2 * (𝓡).E := a_eq p v
  have hGn : (𝓡).Gn = (𝓡).E * (1 + (𝓡).a) := by rw [Gn_def, F0_def]; ring
  have hE1 : 1 ≤ (𝓡).E := hdisc _ hE
  have ha18 : 18 ≤ (𝓡).a := by
    rw [ha]
    have : (𝓡).Delta * (𝓡).U ^ 2 ≤ (𝓡).Delta * (𝓡).U ^ 2 * (𝓡).E :=
      le_mul_of_one_le_right (by linarith) hE1
    linarith
  have e1 : (3 * g) ^ 2 = 9 * ((𝓡).E * (1 + (𝓡).a)) := by rw [← hGn, hG]; ring
  have e2 : (𝓡).a ^ 2 = (𝓡).Delta * (𝓡).U ^ 2 * (𝓡).E * (𝓡).a := by rw [ha]; ring
  have h9 : 9 * (1 + (𝓡).a) < (𝓡).Delta * (𝓡).U ^ 2 * (𝓡).a := by nlinarith
  have hsq : (3 * g) ^ 2 < (𝓡).a ^ 2 := by
    rw [e1, e2]
    have := mul_lt_mul_of_pos_left h9 hE
    nlinarith
  by_contra hn
  push_neg at hn
  have ha0 : 0 < (𝓡).a := by linarith
  have := mul_le_mul hn hn ha0.le (by linarith)
  nlinarith

/-- The transport estimate (4.3): `2|z| < V²` when `|z| = g y`. -/
theorem two_abs_z_lt {g y z : R} (hg : 0 < g) (hy : 0 < y) (hz : |z| = g * y)
    (h3g : 3 * g < (𝓡).a) (hac : (𝓡).a < (𝓡).f - (𝓡).c) (hfV : (𝓡).f - (𝓡).c ≤ |(𝓡).V|)
    (h2y : 2 * y < 3 * |(𝓡).V|) : 2 * |z| < (𝓡).V ^ 2 := by
  rw [hz]
  have hV : 3 * g < |(𝓡).V| := by linarith
  have e : (𝓡).V ^ 2 = |(𝓡).V| * |(𝓡).V| := by rw [← sq_abs]; ring
  rw [e]
  have h1 : g * (2 * y) < g * (3 * |(𝓡).V|) := mul_lt_mul_of_pos_left h2y hg
  have h2 : 3 * g * |(𝓡).V| < |(𝓡).V| * |(𝓡).V| :=
    mul_lt_mul_of_pos_right hV (by linarith)
  nlinarith

/-- **`B ≥ 0`** (§5): a negative `B` makes the carrier `Z` too large for `|z| < L/2`. -/
theorem B_nonneg (hdisc : ∀ x : R, 0 < x → 1 ≤ x) {z : R}
    (hh : 0 < (𝓡).h) (hX : 0 < (𝓡).X) (hY : 0 < (𝓡).Y) (hD2 : 2 ≤ (𝓡).X * (𝓡).Y)
    (hH : 0 < (𝓡).H) (hn : 0 < v 7) (hK : 0 < (𝓡).K)
    (hZ : (𝓡).Z = (𝓡).M * z) (hz : 2 * |z| < (𝓡).V ^ 2)
    (he : (𝓡).e < |(𝓡).b|) (hbV : |(𝓡).b| < (𝓡).V ^ 2) : 0 ≤ (𝓡).B := by
  by_contra hB
  push_neg at hB
  have hBn : 1 ≤ -(𝓡).B := hdisc _ (by linarith)
  have hZd := Z_def p v
  have hMd := M_def p v
  set h := (𝓡).h
  set X := (𝓡).X
  set Y := (𝓡).Y
  set H := (𝓡).H
  set B := (𝓡).B
  set VV := (𝓡).V * (𝓡).V
  have hVV : (𝓡).V ^ 2 = VV := by rw [sq]
  rw [hVV] at hz hbV
  have hD : 0 < X * Y := mul_pos hX hY
  have hhD : 0 < h * (X * Y) := mul_pos hh hD
  have hhDH : 0 < h * (X * Y) * H := mul_pos hhD hH
  have hVV0 : 0 ≤ VV := mul_self_nonneg _
  have t1 : 0 < h * (X * Y) * H * v 7 := mul_pos hhDH hn
  have t2 : h * (X * Y) * H * VV ≤ h * (X * Y) * H * VV * -B :=
    le_mul_of_one_le_right (mul_nonneg hhDH.le hVV0) hBn
  have t3 : 0 < h * (X * Y) * (𝓡).K := mul_pos hhD hK
  have t4 : H * (X * Y) ≤ H * (X * Y) * -B := le_mul_of_one_le_right (mul_pos hH hD).le hBn
  have t5 : H * h * (𝓡).e < H * h * |(𝓡).b| := mul_lt_mul_of_pos_left he (mul_pos hH hh)
  have hM : (𝓡).M = h * (X * Y) * H := hMd
  have up1 : (𝓡).M * z ≤ (𝓡).M * |z| := mul_le_mul_of_nonneg_left (le_abs_self z) (by rw [hM]; exact hhDH.le)
  have up2 : (𝓡).M * (2 * |z|) < (𝓡).M * VV := mul_lt_mul_of_pos_left hz (by rw [hM]; exact hhDH)
  have m1 : 2 * (H * h) * |(𝓡).b| < 2 * (H * h) * VV :=
    mul_lt_mul_of_pos_left hbV (by have := mul_pos hH hh; linarith)
  have m2 : 2 * (h * H * VV) ≤ (X * Y) * (h * H * VV) :=
    mul_le_mul_of_nonneg_right hD2 (mul_nonneg (mul_pos hh hH).le hVV0)
  rw [hM] at up1 up2
  rw [hZ, hM] at hZd
  nlinarith

/-- **`C > 0`** from `B ≥ 0`, `F > 0` and `K0 + w > 0`. -/
theorem C_pos (hB : 0 ≤ (𝓡).B) (hF : 0 < v 1) (hKw : 0 < p 1 + v 5) : 0 < (𝓡).C := by
  have hBd := B_def p v
  by_contra hC
  push_neg at hC
  have : (p 1 + v 5) * (𝓡).C ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hKw.le hC
  linarith

/-- **Stage K7 for the 75/402 circuit.** From the root-stage outputs and the
elementary register sizes, every zero has `B ≥ 0` and `C > 0`. -/
theorem transport (hdisc : ∀ x : R, 0 < x → 1 ≤ x) {g y z : R}
    (hg : 0 < g) (hy : 0 < y) (hzgy : |z| = g * y) (hG : (𝓡).Gn = g ^ 2)
    (hZ : (𝓡).Z = (𝓡).M * z)
    (hnorm : (𝓡).Q * (𝓡).V ^ 2 - ((𝓡).Q - 1) * y ^ 2 = 1)
    (hc : 2 ≤ (𝓡).c) (hck : (𝓡).k < (𝓡).c) (hQ : (𝓡).c ^ 2 < (𝓡).Q)
    (hac : (𝓡).a + (𝓡).c < (𝓡).f) (hfc : 2 * (𝓡).c < (𝓡).f)
    (hE : 0 < (𝓡).E) (hDU : 18 ≤ (𝓡).Delta * (𝓡).U ^ 2)
    (hT : 1 ≤ v 4) (hh : 0 < (𝓡).h) (hX : 0 < (𝓡).X) (hY : 0 < (𝓡).Y)
    (hD2 : 2 ≤ (𝓡).X * (𝓡).Y) (hH : 0 < (𝓡).H) (hn : 0 < v 7) (hK : 0 < (𝓡).K)
    (hF : 0 < v 1) (hKw : 0 < p 1 + v 5) :
    0 ≤ (𝓡).B ∧ 0 < (𝓡).C := by
  have hb := b_ne_zero p v hdisc hnorm hc hQ
  obtain ⟨hfV, hbV⟩ := abs_V_bounds p v hdisc hb (by linarith) hfc
  have hQ2 : 2 ≤ (𝓡).Q := by nlinarith
  have h2y := two_y_lt p v hy hQ2 hnorm
  have h3g := three_g_lt_a p v hdisc hg hG hE hDU
  have hz := two_abs_z_lt p v hg hy hzgy h3g (by linarith) hfV h2y
  have hV1 : 1 ≤ |(𝓡).V| := by have := hdisc _ (abs_pos.mpr hb); linarith
  have hbV2 : |(𝓡).b| < (𝓡).V ^ 2 := by
    have e : (𝓡).V ^ 2 = |(𝓡).V| * |(𝓡).V| := by rw [← sq_abs]; ring
    rw [e]; nlinarith
  have he : (𝓡).e < |(𝓡).b| := lt_of_lt_of_le (e_lt_b p v hT (by linarith) hck) (le_abs_self _)
  have hB := B_nonneg p v hdisc hh hX hY hD2 hH hn hK hZ hz he hbV2
  exact ⟨hB, C_pos p v hB hF hKw⟩

end DiophantineConsistency.TenPositiveTransport
