import DiophantineConsistency.Z10.Z10Bootstrap
import DiophantineConsistency.ZRows.CoprimeSquares

/-! # The norm split and the square roots of the ten-integer guard

Package 106, integer lane (steps S3 and S5 of the route). `𝓡 = Z10Regs.regs p x` at a signed
assignment `x : Fin 10 → DiffRing V` in a model `V` of `𝗜𝚺₁`; no port fact is used.

* `norm_split`: at a zero of the polar value, `a0 = r₁²`, `a1 = s₁²` and
  `Theta = Sigma · (m − r₁ − s₁)` (`N9Norm.roots_of_norm2_zero`; `Sigma ≠ 0` and `a0 ≠ a1` are
  `Z10Bootstrap.Sigma_ne`, `a0_ne_a1`). In particular `Sigma ∣ Theta` (`Sigma_dvd_Theta`).
* `a0_factor`, `bez_r_cof`: `a0 = r · cof` with `cof = 1 + (9 Delta − 3) r z²`, and
  `r · (−(9 Delta − 3) z²) + cof = 1`.
* `bez_b_Q`: `r = b Q` and `Q ≡ 1 (mod b²)` give `b · (−b c) + Q = 1`.
* `neg_sq_ne_mod3`, `pos_of_mod3`: a negative square is not `1 (mod 3)`; hence an element
  `≡ 1 (mod 3)` whose absolute value is a square is positive.
* `roots`: at a zero, `b = β²`, `Q = q²`, `r = d²`, `cof = e²` with positive `β, q, d, e : V`.
  The absolute values are squares by coprimality (`ZRowsCoprimeSquares.abs_squares_of_mul_square`);
  `r, b, Q ≡ 1 (mod 3)` are positive; `cof` is positive because `r · cof = a0 = r₁² ≠ 0`.
* `Delta_pos`: at a zero `Delta > 0`. If `Delta ≤ 0` then `9 Delta − 3 ≤ −3`, and `r z² ≥ 1`
  makes `cof ≤ −2`. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.Z10Squares
open Nine121 Nine121.N105Layout Z10Regs Z10Bootstrap
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing
open ZRowsCoprimeSquares (abs_squares_of_mul_square)
open P138Bootstrap (one_le_of_pos' one_le_abs)

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Residues modulo three -/

theorem mod3_split (d : V) : ∃ t : V, d = 3 * t ∨ d = 3 * t + 1 ∨ d = 3 * t + 2 := by
  have hlt : d % 3 < 2 + 1 := by
    have h := Arithmetic.mod_lt d (show (0 : V) < 3 by simp)
    rwa [← two_add_one_eq_three] at h
  have hle : d % 3 ≤ 2 := lt_succ_iff_le.mp hlt
  have hd := Arithmetic.div_add_mod d 3
  rcases le_two_iff_eq_zero_or_one_or_two.mp hle with h | h | h
  · exact ⟨d / 3, Or.inl (by rw [h, add_zero] at hd; exact hd.symm)⟩
  · exact ⟨d / 3, Or.inr (Or.inl (by rw [h] at hd; exact hd.symm))⟩
  · exact ⟨d / 3, Or.inr (Or.inr (by rw [h] at hd; exact hd.symm))⟩

/-- A negative square is not `1 (mod 3)`. -/
theorem neg_sq_ne_mod3 (d : V) (m : DiffRing V) : -(ι d * ι d) ≠ 3 * m + 1 := by
  intro h
  apply three_not_dvd_one (V := V)
  obtain ⟨t, rfl | rfl | rfl⟩ := mod3_split d
  · simp only [map_mul, map_ofNat] at h
    exact ⟨-(3 * ι t * ι t) - m, by linear_combination -h⟩
  · simp only [map_add, map_mul, map_ofNat, map_one] at h
    exact ⟨1 + 3 * ι t * ι t + 2 * ι t + m, by linear_combination h⟩
  · simp only [map_add, map_mul, map_ofNat] at h
    exact ⟨2 + 3 * ι t * ι t + 4 * ι t + m, by linear_combination h⟩

/-- An element `≡ 1 (mod 3)` whose absolute value is a square is positive. -/
theorem pos_of_mod3 {Z : DiffRing V} {d : V} (h3 : (3 : DiffRing V) ∣ Z - 1)
    (hd : |Z| = ι d * ι d) : 0 < Z := by
  obtain ⟨m, hm⟩ := h3
  have hZ0 : Z ≠ 0 := by
    intro h0
    rw [h0] at hm
    exact three_not_dvd_one ⟨-m, by linear_combination -hm⟩
  rcases lt_or_gt_of_ne hZ0 with hneg | hpos
  · exfalso
    rw [abs_of_neg hneg] at hd
    apply neg_sq_ne_mod3 d m
    rw [← hd, neg_neg]
    linear_combination hm
  · exact hpos

/-- A positive element whose absolute value is a square of a natural is the square of a positive
natural. -/
theorem pos_root {Z : DiffRing V} {a : V} (hZ : 0 < Z) (ha : |Z| = ι a * ι a) :
    0 < a ∧ Z = ι a * ι a := by
  rw [abs_of_pos hZ] at ha
  refine ⟨?_, ha⟩
  rcases eq_zero_or_pos a with h0 | h0
  · rw [h0, map_zero, mul_zero] at ha; exact absurd ha hZ.ne'
  · exact h0

/-! ## The registers -/

section Regs
variable (p : Fin 4 → DiffRing V) (x : Fin 10 → DiffRing V)
local notation "𝓡" => regs p x

/-- The cofactor of `r` in the guard radicand `a0`. -/
def cof : DiffRing V := 1 + (9 * (𝓡).Delta - 3) * ((𝓡).r * x 8 ^ 2)

theorem a0_factor : (𝓡).a0 = (𝓡).r * cof p x := by unfold cof; rw [a0_def]; ring

theorem bez_r_cof : ∃ α β : DiffRing V, (𝓡).r * α + cof p x * β = 1 :=
  ⟨-((9 * (𝓡).Delta - 3) * x 8 ^ 2), 1, by unfold cof; ring⟩

theorem bez_b_Q : ∃ α β : DiffRing V, (𝓡).b * α + (𝓡).Q * β = 1 := by
  obtain ⟨c, hc⟩ := Q_mod_bb p x
  exact ⟨-((𝓡).b * c), 1, by linear_combination hc⟩

theorem a0_ne : (𝓡).a0 ≠ 0 := by
  intro h
  obtain ⟨c, hc⟩ := a0_mod3 p x
  rw [h] at hc
  exact three_not_dvd_one ⟨-c, by linear_combination -hc⟩

/-- **The norm split.** At a zero both radicands are squares and the centre is their sum of
roots. -/
theorem norm_split (hz : value p x = 0) :
    ∃ r1 s1 : DiffRing V, (𝓡).a0 = r1 ^ 2 ∧ (𝓡).a1 = s1 ^ 2 ∧
      (𝓡).Theta = (𝓡).Sigma * (x 9 - r1 - s1) := by
  have hz' := hz
  rw [value_def] at hz'
  obtain ⟨r1, s1, h0, h1, h⟩ :=
    N9Norm.roots_of_norm2_zero (Sigma_ne p x hz) (a0_ne_a1 p x) hz'
  exact ⟨r1, s1, h0, h1, by linear_combination -h⟩

theorem Sigma_dvd_Theta (hz : value p x = 0) : (𝓡).Sigma ∣ (𝓡).Theta := by
  obtain ⟨r1, s1, _, _, h⟩ := norm_split p x hz
  exact ⟨_, h⟩

/-- At a zero the Lucas radicand is a square. -/
theorem a1_square (hz : value p x = 0) : ∃ s1 : DiffRing V, (𝓡).a1 = s1 ^ 2 := by
  obtain ⟨_, s1, _, h, _⟩ := norm_split p x hz
  exact ⟨s1, h⟩

theorem r_pos (hz : value p x = 0) : 0 < (𝓡).r := by
  obtain ⟨r1, _, h0, _, _⟩ := norm_split p x hz
  have hprod : (𝓡).r * cof p x = r1 * r1 := by rw [← a0_factor p x, h0]; ring
  obtain ⟨⟨d, hd⟩, _⟩ := abs_squares_of_mul_square (bez_r_cof p x) hprod
  exact pos_of_mod3 (r_mod3 p x) hd

theorem cof_pos (hz : value p x = 0) : 0 < cof p x := by
  obtain ⟨r1, _, h0, _, _⟩ := norm_split p x hz
  have hr := r_pos p x hz
  have hprod : (𝓡).r * cof p x = r1 * r1 := by rw [← a0_factor p x, h0]; ring
  have hc0 : cof p x ≠ 0 := by
    intro h
    apply a0_ne p x
    rw [a0_factor, h, mul_zero]
  have h2 := mul_self_nonneg r1
  rw [← hprod] at h2
  have h3 : 0 ≤ cof p x := by
    by_contra hn
    have : (𝓡).r * cof p x < 0 := mul_neg_of_pos_of_neg hr (lt_of_not_ge hn)
    linarith
  exact lt_of_le_of_ne h3 (Ne.symm hc0)

/-- **The square roots.** At a zero, `b = β²`, `Q = q²`, `r = d²` and `cof = e²` with positive
`β, q, d, e`. -/
theorem roots (hz : value p x = 0) :
    ∃ β q d e : V, 0 < β ∧ 0 < q ∧ 0 < d ∧ 0 < e ∧ (𝓡).b = ι β * ι β ∧ (𝓡).Q = ι q * ι q ∧
      (𝓡).r = ι d * ι d ∧ cof p x = ι e * ι e := by
  obtain ⟨r1, _, h0, _, _⟩ := norm_split p x hz
  have hprod : (𝓡).r * cof p x = r1 * r1 := by rw [← a0_factor p x, h0]; ring
  obtain ⟨⟨d, hd⟩, ⟨e, he⟩⟩ := abs_squares_of_mul_square (bez_r_cof p x) hprod
  obtain ⟨hd0, hrd⟩ := pos_root (r_pos p x hz) hd
  obtain ⟨he0, hce⟩ := pos_root (cof_pos p x hz) he
  have hbQ : (𝓡).b * (𝓡).Q = ι d * ι d := by rw [← hrd, r_def]
  obtain ⟨⟨β, hβ⟩, ⟨q, hq⟩⟩ := abs_squares_of_mul_square (bez_b_Q p x) hbQ
  obtain ⟨hβ0, hbβ⟩ := pos_root (pos_of_mod3 (b_mod3 p x) hβ) hβ
  obtain ⟨hq0, hQq⟩ := pos_root (pos_of_mod3 (Q_mod3 p x) hq) hq
  exact ⟨β, q, d, e, hβ0, hq0, hd0, he0, hbβ, hQq, hrd, hce⟩

theorem b_pos (hz : value p x = 0) : 0 < (𝓡).b := by
  obtain ⟨β, _, _, _, hβ, _, _, _, hb, _, _, _⟩ := roots p x hz
  rw [hb]
  have : (0 : DiffRing V) < ι β := by rw [← map_zero ι]; exact ι_lt_ι.mpr hβ
  exact mul_pos this this

theorem Q_pos (hz : value p x = 0) : 0 < (𝓡).Q := by
  obtain ⟨_, q, _, _, _, hq, _, _, _, hQ, _, _⟩ := roots p x hz
  rw [hQ]
  have : (0 : DiffRing V) < ι q := by rw [← map_zero ι]; exact ι_lt_ι.mpr hq
  exact mul_pos this this

/-- **The guard discriminant is positive at a zero.** -/
theorem Delta_pos (hz : value p x = 0) : 0 < (𝓡).Delta := by
  have hr := one_le_of_pos' (r_pos p x hz)
  have hz2 : 1 ≤ x 8 ^ 2 := by
    have := one_le_abs (z_x_ne p x hz).1
    rw [← sq_abs]; nlinarith
  have hc := cof_pos p x hz
  by_contra hn
  have hD : 9 * (𝓡).Delta - 3 ≤ -3 := by linarith [not_lt.mp hn]
  have h1 : 1 ≤ (𝓡).r * x 8 ^ 2 := by
    nlinarith [mul_nonneg (show (0 : DiffRing V) ≤ (𝓡).r - 1 by linarith)
      (show (0 : DiffRing V) ≤ x 8 ^ 2 - 1 by linarith)]
  have h3 := mul_nonneg (show (0 : DiffRing V) ≤ -3 - (9 * (𝓡).Delta - 3) by linarith)
    (show (0 : DiffRing V) ≤ (𝓡).r * x 8 ^ 2 - 1 by linarith)
  unfold cof at hc
  nlinarith

end Regs

#print axioms neg_sq_ne_mod3
#print axioms norm_split
#print axioms roots
#print axioms Delta_pos

end DiophantineConsistency.Z10Squares
