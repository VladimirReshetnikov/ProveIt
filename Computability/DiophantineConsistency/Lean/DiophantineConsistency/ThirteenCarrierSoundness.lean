import DiophantineConsistency.ThirteenCarrier
import DiophantineConsistency.Carrier65
import DiophantineConsistency.SignedPellResidue

/-!
# Soundness of every positive thirteen-coordinate carrier zero

The map restores the transport coordinate and replaces the signed auxiliary
ordinate by its absolute value. It proves an actual positive Carrier65 zero,
without a native interpretation or fresh-seed completeness assumption.
-/

namespace DiophantineConsistency.ThirteenCarrierSoundness

variable {R : Type*} [CommRing R]

def b (p : Fin 4 → R) (v : Fin 13 → R) : R := p 0 * v 0

/-- Insert z and y, and multiply the parent's i by b exactly once. -/
def parent (p : Fin 4 → R) (v : Fin 13 → R) (z y : R) (j : Fin 14) : R :=
  match j.val with
  | 0 => v 0
  | 1 => v 1
  | 2 => v 2
  | 3 => z
  | 4 => v 3
  | 5 => b p v * v 4
  | 6 => v 5
  | 7 => v 6
  | 8 => v 7
  | 9 => v 8
  | 10 => v 9
  | 11 => v 10
  | 12 => y
  | _ => v 12

/-- Common blocks, evaluated at irrelevant positive placeholders z=y=1. -/
def data (p : Fin 4 → R) (v : Fin 13 → R) : Carrier65.Core R :=
  Carrier65.core p (parent p v 1 1)

def G (p : Fin 4 → R) (v : Fin 13 → R) : R :=
  (p 1 + v 7) * (data p v).C - v 1

def signedY (p : Fin 4 → R) (v : Fin 13 → R) : R := (ThirteenCarrier.core p v).y

def auxiliary (p : Fin 4 → R) (v : Fin 13 → R) : R :=
  (data p v).S ^ 2 * ((data p v).V ^ 2 - signedY p v ^ 2) + signedY p v ^ 2

theorem signedY_shape (p : Fin 4 → R) (v : Fin 13 → R) :
    signedY p v = 1 + 4 * (b p v * (v 11 - (data p v).V ^ 2 * G p v) - G p v) := rfl

theorem scale_shape (p : Fin 4 → R) (v : Fin 13 → R) :
    (ThirteenCarrier.core p v).delta * (ThirteenCarrier.core p v).t = (data p v).S := by
  change (data p v).delta * (b p v * v 4 * (data p v).c ^ 2) =
    (b p v * v 4) * (data p v).delta * (data p v).c ^ 2
  ring

theorem core_parent (p : Fin 4 → R) (v : Fin 13 → R) (z y : R) :
    Carrier65.core p (parent p v z y) =
      { data p v with
        U := (data p v).S ^ 2 * ((data p v).V ^ 2 - y ^ 2) + y ^ 2
        W := G p v + (data p v).q - z * b p v
        y := y } := by
  dsimp only [data, Carrier65.core]
  congr 1; first | rfl | (dsimp [G, data, parent, Carrier65.core, b]; ring_nf; abel)

theorem value69_scaled (p : Fin 4 → R) (v : Fin 13 → R) :
    ThirteenCarrier.value69 p v = (data p v).delta *
      ((data p v).P * (data p v).Q * auxiliary p v * Carrier65.strong (data p v) - 1) := by
  dsimp only [ThirteenCarrier.value69]
  rw [scale_shape]
  change (data p v).P * (data p v).Q * auxiliary p v *
    ((data p v).delta * (data p v).f ^ 2 - (data p v).S ^ 2) - (data p v).delta = _
  change (data p v).P * (data p v).Q * auxiliary p v *
    (data p v).Z - (data p v).delta = _
  rw [show (data p v).Z = (data p v).delta * Carrier65.strong (data p v) from
    Carrier65.strong_scale p (parent p v 1 1)]
  ring

theorem parent_pos (p : Fin 4 → ℤ) (v : Fin 13 → ℤ) (hb : 0 < p 0)
    (hv : ∀ j, 0 < v j) {z y : ℤ} (hz : 0 < z) (hy : 0 < y) :
    ∀ j, 0 < parent p v z y j := by
  have hi : 0 < b p v * v 4 := mul_pos (mul_pos hb (hv 0)) (hv 4)
  intro j
  fin_cases j <;> first
    | exact hz
    | exact hy
    | exact hi
    | exact hv 0
    | exact hv 1
    | exact hv 2
    | exact hv 3
    | exact hv 5
    | exact hv 6
    | exact hv 7
    | exact hv 8
    | exact hv 9
    | exact hv 10
    | exact hv 12

theorem norms_of_zero (p : Fin 4 → ℤ) (v : Fin 13 → ℤ) (hb : 0 < p 0)
    (hv : ∀ j, 0 < v j) (hz : ThirteenCarrier.value69 p v = 0) :
    (data p v).P = 1 ∧ (data p v).Q = 1 ∧ auxiliary p v = 1 ∧
      Carrier65.strong (data p v) = 1 := by
  have hp := parent_pos p v hb hv (z := 1) (y := 1) (by norm_num) (by norm_num)
  have hd := Carrier65.delta_pos p (parent p v 1 1) hb hp
  have hP : (data p v).P ≠ -1 := by
    change (Carrier65.core p (parent p v 1 1)).P ≠ -1
    rw [Carrier65.first_shape]
    exact ConsecutivePell.norm_ne_neg_one _ _ _
      (Carrier65.firstParameter_ge_two p (parent p v 1 1) hb hp)
  have hQ : (data p v).Q ≠ -1 := by
    change (data p v).D ^ 2 - (data p v).delta * (data p v).c ^ 2 ≠ -1
    rw [show (data p v).delta = ((data p v).a + 2) ^ 2 - 1 from
      Carrier65.delta_shape p (parent p v 1 1)]
    exact ShortEquation.strong_ne_neg_one _ _ _
  have hs : Carrier65.strong (data p v) ≠ -1 := by
    unfold Carrier65.strong
    rw [show (data p v).delta = ((data p v).a + 2) ^ 2 - 1 from
      Carrier65.delta_shape p (parent p v 1 1)]
    exact ShortEquation.strong_ne_neg_one _ _ _
  have hu : auxiliary p v ≠ -1 := ShortSystem.square_aux_ne_neg_one _ _ _
  rw [value69_scaled, mul_eq_zero] at hz
  have hprod : (data p v).P * (data p v).Q * auxiliary p v *
      Carrier65.strong (data p v) = 1 := sub_eq_zero.mp (hz.resolve_left (ne_of_gt hd))
  have h := (ShortSystem.product_eq_one_iff (data p v).P (data p v).Q
    (auxiliary p v) 1 1 (Carrier65.strong (data p v)) hP hQ hs (fun _ => hu)).mp
      (by simpa only [mul_one] using hprod)
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

theorem scale_ge_two (p : Fin 4 → ℤ) (v : Fin 13 → ℤ) (hb : 0 < p 0)
    (hv : ∀ j, 0 < v j) : 2 ≤ (data p v).S := by
  have hp := parent_pos p v hb hv (z := 1) (y := 1) (by norm_num) (by norm_num)
  have hY := (Carrier65.scales_pos p (parent p v 1 1) hb hp).2.1
  have hd := Carrier65.delta_pos p (parent p v 1 1) hb hp
  have hi : 0 < (data p v).i := mul_pos (mul_pos hb (hv 0)) (hv 4)
  have hk : 2 ≤ (data p v).k := by change 2 ≤ v 9 + v 10; have := hv 9; have := hv 10; omega
  have hc : 2 ≤ (data p v).c := by
    change 2 ≤ (data p v).k * (data p v).Y + v 9
    have := hv 9
    change 0 < (data p v).Y at hY
    nlinarith
  have hid : 0 < (data p v).i * (data p v).delta := mul_pos hi hd
  change 2 ≤ ((data p v).i * (data p v).delta) * (data p v).c ^ 2
  have hc2 : 4 ≤ (data p v).c ^ 2 := by nlinarith
  nlinarith

theorem auxiliary_norm (p : Fin 4 → ℤ) (v : Fin 13 → ℤ)
    (hu : auxiliary p v = 1) :
    (data p v).S ^ 2 * (data p v).V ^ 2 -
      ((data p v).S ^ 2 - 1) * signedY p v ^ 2 = 1 := by
  unfold auxiliary at hu
  nlinarith only [hu]

/-- Both estimates follow from the norm itself, with no sign assumptions on V,y. -/
theorem auxiliary_estimates {S V y : ℤ} (hS : 2 ≤ S)
    (hn : S ^ 2 * V ^ 2 - (S ^ 2 - 1) * y ^ 2 = 1) :
    y ≠ 0 ∧ |y| < 2 * |V| := by
  have hS2 : 4 ≤ S ^ 2 := by nlinarith
  have hV : V ≠ 0 := by
    intro hV
    rw [hV] at hn
    have hm := mul_nonneg (by omega : 0 ≤ S ^ 2 - 1) (sq_nonneg y)
    norm_num at hn
    linarith
  have hV2 : 1 ≤ V ^ 2 := sq_pos_of_ne_zero hV
  have hy : y ≠ 0 := by
    intro hy
    rw [hy] at hn
    have hm := mul_le_mul_of_nonneg_right hS2 (sq_nonneg V)
    norm_num at hn
    nlinarith
  refine ⟨hy, ?_⟩
  have hsq : y ^ 2 < 4 * V ^ 2 := by
    by_contra h
    have h1 := mul_nonneg (by omega : 0 ≤ S ^ 2 - 1)
      (by omega : 0 ≤ y ^ 2 - 4 * V ^ 2)
    have h2 := mul_nonneg (by omega : 0 ≤ 3 * S ^ 2 - 4) (sq_nonneg V)
    nlinarith only [hn, h1, h2]
  by_contra h
  have h1 := mul_nonneg (by omega : 0 ≤ |y| - 2 * |V|)
    (show 0 ≤ |y| + 2 * |V| by positivity)
  nlinarith [sq_abs y, sq_abs V]

/-- The positive carrier m forces the recovered transport to be nonnegative. -/
theorem transport_nonneg {b m G V y : ℤ} (hb : 0 < b) (hm : 0 < m)
    (hy : y = 1 + 4 * (b * (m - V ^ 2 * G) - G))
    (hsmall : |y| < 2 * |V|) : 0 ≤ G := by
  by_contra hG
  have hG : G ≤ -1 := by omega
  have hV : 1 ≤ |V| := by have := abs_nonneg y; omega
  have hVs : |V| ≤ V ^ 2 := by
    have hh := mul_nonneg (abs_nonneg V) (by omega : 0 ≤ |V| - 1)
    nlinarith [sq_abs V]
  have hbm : 1 ≤ b * m := mul_pos hb hm
  have hterm := mul_le_mul_of_nonneg_right (show 1 ≤ b from hb) (sq_nonneg V)
  have hprod := mul_nonneg (show 0 ≤ 1 + b * V ^ 2 by positivity)
    (by omega : 0 ≤ -G - 1)
  nlinarith [le_abs_self y]

theorem base_dvd_transport (p : Fin 4 → ℤ) (v : Fin 13 → ℤ) (hb : 0 < p 0)
    (hv : ∀ j, 0 < v j) (hu : auxiliary p v = 1) : b p v ∣ G p v := by
  have hs := scale_ge_two p v hb hv
  have hn := auxiliary_norm p v hu
  have hy4 : signedY p v ≡ 1 [ZMOD 4] := by
    rw [signedY_shape]
    exact (Int.modEq_iff_dvd.mpr ⟨-(b p v * (v 11 - (data p v).V ^ 2 * G p v) - G p v), by ring⟩)
  have hdiv := SignedPellResidue.four_square_dvd_sub_one hs hn hy4
  rw [signedY_shape] at hdiv
  have hdiv' : (data p v).S ^ 2 ∣ b p v * (v 11 - (data p v).V ^ 2 * G p v) - G p v := by
    apply (mul_dvd_mul_iff_left (by norm_num : (4 : ℤ) ≠ 0)).mp
    simpa only [add_sub_cancel_left] using hdiv
  have hbS : b p v ∣ (data p v).S := by
    refine ⟨v 4 * (data p v).delta * (data p v).c ^ 2, ?_⟩
    change (b p v * v 4) * (data p v).delta * (data p v).c ^ 2 = _
    ring
  have hbS2 : b p v ∣ (data p v).S ^ 2 := dvd_trans hbS (dvd_pow_self _ (by decide : 2 ≠ 0))
  have hsub := dvd_trans hbS2 hdiv'
  have hleft : b p v ∣ b p v * (v 11 - (data p v).V ^ 2 * G p v) := dvd_mul_right _ _
  have h := dvd_sub hleft hsub
  simpa only [sub_sub_cancel] using h

/-- Division occurs only in this witness construction, after divisibility is proved. -/
def restored (p : Fin 4 → ℤ) (v : Fin 13 → ℤ) : Fin 14 → ℤ :=
  parent p v (G p v / b p v + 1) |signedY p v|

/-- Every positive zero of the literal 69 profile gives a positive Carrier65 zero. -/
theorem restores_positive_zero69 (p : Fin 4 → ℤ) (v : Fin 13 → ℤ) (hb : 0 < p 0)
    (hv : ∀ j, 0 < v j) (hz : ThirteenCarrier.value69 p v = 0) :
    (∀ j, 0 < restored p v j) ∧ Carrier65.value p (restored p v) = 0 := by
  obtain ⟨hP, hQ, hu, hs⟩ := norms_of_zero p v hb hv hz
  have hbv : 0 < b p v := mul_pos hb (hv 0)
  obtain ⟨hyne, hsmall⟩ := auxiliary_estimates (scale_ge_two p v hb hv) (auxiliary_norm p v hu)
  have hG := transport_nonneg hbv (hv 11) (signedY_shape p v) hsmall
  have hdiv := base_dvd_transport p v hb hv hu
  have hquot : G p v / b p v * b p v = G p v := Int.ediv_mul_cancel hdiv
  have hzpos : 0 < G p v / b p v + 1 := by
    have := Int.ediv_nonneg hG hbv.le
    omega
  have hW : G p v + (data p v).q - (G p v / b p v + 1) * b p v = 1 := by
    change G p v + (b p v + 1) - (G p v / b p v + 1) * b p v = 1
    nlinarith only [hquot]
  have hZ : (data p v).Z = (data p v).delta := by
    change (Carrier65.core p (parent p v 1 1)).Z = _
    rw [Carrier65.strong_scale]
    change (data p v).delta * Carrier65.strong (data p v) = (data p v).delta
    rw [hs, mul_one]
  refine ⟨parent_pos p v hb hv hzpos (abs_pos.mpr hyne), ?_⟩
  unfold restored Carrier65.value
  rw [core_parent]
  change (data p v).P * (data p v).Q *
    ((data p v).S ^ 2 * ((data p v).V ^ 2 - |signedY p v| ^ 2) + |signedY p v| ^ 2) *
    (G p v + (data p v).q - (G p v / b p v + 1) * b p v) * (data p v).Z -
    (data p v).delta = 0
  rw [sq_abs]
  change (data p v).P * (data p v).Q * auxiliary p v *
    (G p v + (data p v).q - (G p v / b p v + 1) * b p v) * (data p v).Z -
    (data p v).delta = 0
  rw [hP, hQ, hu, hW, hZ]
  ring

theorem restores_positive_zero70 (p : Fin 4 → ℤ) (v : Fin 13 → ℤ) (hb : 0 < p 0)
    (hv : ∀ j, 0 < v j) (hz : ThirteenCarrier.value70 p v = 0) :
    (∀ j, 0 < restored p v j) ∧ Carrier65.value p (restored p v) = 0 := by
  have he := ThirteenCarrier.positive_zero_sets p v hb hv
  exact restores_positive_zero69 p v hb hv (he.1.mpr (he.2.mp hz))

theorem restores_positive_zero71 (p : Fin 4 → ℤ) (v : Fin 13 → ℤ) (hb : 0 < p 0)
    (hv : ∀ j, 0 < v j) (hz : ThirteenCarrier.value71 p v = 0) :
    (∀ j, 0 < restored p v j) ∧ Carrier65.value p (restored p v) = 0 := by
  exact restores_positive_zero69 p v hb hv
    ((ThirteenCarrier.positive_zero_sets p v hb hv).1.mpr hz)

/-- The endpoint mentions the actual polynomials and the explicit restored assignment. -/
theorem polynomial_zero_restores (p : Fin 4 → ℤ) (v : Fin 13 → ℤ) (hb : 0 < p 0)
    (hv : ∀ j, 0 < v j)
    (hz : MvPolynomial.eval v (ThirteenCarrier.polynomial69 p) = 0 ∨
      MvPolynomial.eval v (ThirteenCarrier.polynomial70 p) = 0 ∨
      MvPolynomial.eval v (ThirteenCarrier.polynomial71 p) = 0) :
    (∀ j, 0 < restored p v j) ∧
      MvPolynomial.eval (restored p v) (Carrier65.polynomial p) = 0 := by
  rw [Carrier65.eval_polynomial]
  simp only [ThirteenCarrier.eval_polynomial69, ThirteenCarrier.eval_polynomial70,
    ThirteenCarrier.eval_polynomial71] at hz
  rcases hz with hz | hz | hz
  · exact restores_positive_zero69 p v hb hv hz
  · exact restores_positive_zero70 p v hb hv hz
  · exact restores_positive_zero71 p v hb hv hz

end DiophantineConsistency.ThirteenCarrierSoundness
