import DiophantineConsistency.Z10.Z10Guard
import DiophantineConsistency.Z10.Z10Cert

/-! # The Pell indices of `C` and `K` in the ten-integer forms

Package 106, integer lane (steps S8, applied to the registers, and S9 of the route).
`𝓡 = Z10Regs.regs p x` at a signed zero in the ring of differences of a model of `𝗜𝚺₁`.
The only input from the prefix is that the register `X` is a positive natural number,
`X = ι Xn` with `0 < Xn`; no port fact is used.

* `b_ge`, `Y_ge`, `abs_L_ge4`: `b ≥ 4`, `Y ≥ 4`, `|L| ≥ 4` at a zero.
* `one_add_V_ne`: `1 + V ≠ 0` (`V` is even); `three_dvd_halfA`: `3 ∣ A/2`.
* `abs_halfA`: `|A/2| = |L| · X · |1 + V|`; `index_shape`: `2 X + 1 = 4 j + 3`.
* `C_index`: **the certificate at the registers**, `C = ψ_a(2X+1)` with `a + 2 = |A/2|`
  and `2X + 1 < a + 2` (`Z10Cert.cert`).
* `Phalf_ne`, `two_le_abs_Phalf`: `P/2 ≠ 0` and `|P/2| ≥ 2` at a zero.
* `K_index`: `|K| = ψ_p(n)` with `p + 2 = |P/2|`, from the square `Q`
  (`ArithmeticPellClassification.solution_index`). -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.Z10Index
open Nine121 Nine121.N105Layout Z10Regs Z10Bootstrap Z10Squares Z10Guard
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing ZRowsCoprimeSquares ArithmeticPellRecurrence
open P138Bootstrap (one_le_of_pos' one_le_abs)

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable (p : Fin 4 → DiffRing V) (x : Fin 10 → DiffRing V)
local notation "𝓡" => regs p x

/-! ## Elementary sizes -/

theorem b_ge (hz : value p x = 0) : 4 ≤ (𝓡).b := by
  have hb := b_pos p x hz
  rw [b_def] at hb ⊢
  by_contra hcon
  have h0 : 0 < -x 0 := by linarith
  have h1 := one_le_of_pos' h0
  linarith

theorem Y_ge (hz : value p x = 0) : 4 ≤ (𝓡).Y := by
  have hb := b_pos p x hz
  have hY := Y_pos p x hz
  obtain ⟨c, hc⟩ := b_dvd_Y p x
  have hc0 : 0 < c := by
    by_contra hcon
    have h := _root_.mul_nonneg hb.le (neg_nonneg.mpr (not_lt.mp hcon))
    rw [mul_neg, ← hc] at h
    linarith
  have h1 := mul_le_mul_of_nonneg_left (one_le_of_pos' hc0) hb.le
  rw [mul_one, ← hc] at h1
  linarith [b_ge p x hz]

theorem abs_L_ge4 (hz : value p x = 0) : 4 ≤ |(𝓡).L| := by
  have h := abs_L_ge p x hz
  rw [abs_of_pos (Y_pos p x hz)] at h
  linarith [Y_ge p x hz]

theorem one_add_V_ne : 1 + (𝓡).V ≠ 0 :=
  ne_of_two_dvd_succ ⟨2 * (𝓡).g * x 5 * (𝓡).Y + 1, by rw [V_def]; ring⟩

theorem three_dvd_halfA : (3 : DiffRing V) ∣ (𝓡).halfA := by
  rw [halfA_eq]
  exact Dvd.dvd.mul_right ((X_mod3 p x).trans (X_dvd_halfU p x)) _

theorem abs_halfA (Xn : V) (hX : (𝓡).X = ι Xn) :
    |(𝓡).halfA| = |(𝓡).L| * ι Xn * |1 + (𝓡).V| := by
  rw [halfA_eq, halfU_def, hX, _root_.abs_mul, _root_.abs_mul, abs_of_nonneg (ι_nonneg Xn)]

/-- `X` is odd, so `2 X + 1 ≡ 3 (mod 4)`. -/
theorem index_shape (Xn : V) (hX : (𝓡).X = ι Xn) (hX0 : 0 < Xn) :
    ∃ j : V, 2 * Xn + 1 = 4 * j + 3 := by
  obtain ⟨q, hq⟩ := X_odd p x
  have hX1 : (1 : DiffRing V) ≤ ι Xn := by
    have h := (ι_lt_ι (V := V)).mpr hX0
    rw [map_zero] at h
    exact one_le_of_pos' h
  have hq1 : 0 ≤ q - 1 := by
    rw [hX] at hq
    linarith
  obtain ⟨j, hj⟩ := nonneg_iff.mp hq1
  refine ⟨j, ι_injective (V := V) ?_⟩
  simp only [map_add, map_mul, map_one, map_ofNat]
  linear_combination 2 * hq - 2 * hX + 4 * hj

/-! ## The certificate at the registers -/

/-- **The index of `C`**: at a zero with `X = ι Xn > 0`, `C = ψ_a(2X+1)` for the base
`a + 2 = |A/2|`, and the index is below the base. -/
theorem C_index (hz : value p x = 0) (Xn : V) (hX : (𝓡).X = ι Xn) (hX0 : 0 < Xn) :
    ∃ a : V, |(𝓡).halfA| = ι (a + 2) ∧ 2 * Xn + 1 < a + 2 ∧
      (𝓡).C = ι (ycoord (2 * Xn + 1) a) := by
  have hX1 : (1 : DiffRing V) ≤ ι Xn := by
    have h := (ι_lt_ι (V := V)).mpr hX0
    rw [map_zero] at h
    exact one_le_of_pos' h
  have hL := abs_L_ge4 p x hz
  have hV1 := one_le_abs (one_add_V_ne p x)
  -- the size of `A/2`
  have hsize : 2 * ι Xn + 1 < |(𝓡).halfA| := by
    rw [abs_halfA p x Xn hX]
    have h1 := mul_le_mul_of_nonneg_right hL (ι_nonneg Xn)
    have h2 := mul_le_mul_of_nonneg_left hV1
      (_root_.mul_nonneg (abs_nonneg (𝓡).L) (ι_nonneg Xn))
    rw [mul_one] at h2
    linarith
  obtain ⟨a', ha'⟩ := abs_eq_ι (𝓡).halfA
  have ha2 : 0 ≤ ι a' - (2 : DiffRing V) := by
    rw [← ha']
    linarith
  obtain ⟨a, ha⟩ := nonneg_iff.mp ha2
  have hA : |(𝓡).halfA| = ι (a + 2) := by
    rw [ha']
    simp only [map_add, map_ofNat]
    linear_combination ha
  have hB : 2 * Xn + 1 < a + 2 := by
    apply (ι_lt_ι (V := V)).mp
    rw [← hA]
    simp only [map_add, map_mul, map_one, map_ofNat]
    exact hsize
  obtain ⟨j, hj⟩ := index_shape p x Xn hX hX0
  obtain ⟨s1, hs1⟩ := a1_square p x hz
  have hC := one_lt_abs_C p x hz (by linarith)
  refine ⟨a, hA, hB, ?_⟩
  refine Z10Cert.cert (A1 := (𝓡).halfA) (C := (𝓡).C) (ξ := (𝓡).xi)
    (W := 64 * (((𝓡).halfA * (𝓡).halfA - 1) * ((𝓡).C * (𝓡).C) + 1) * (𝓡).C * (𝓡).xi * x 7)
    (D' := ((𝓡).halfA * (𝓡).halfA - 1) * ((𝓡).C * (𝓡).C) + 1)
    (K := 16 * ((𝓡).halfA * (𝓡).halfA - 1) * ((𝓡).C * (𝓡).C * ((𝓡).C * (𝓡).C)) *
      ((𝓡).xi * (𝓡).xi))
    (F := (𝓡).F) (G := (𝓡).G) (H := (𝓡).H) (I := (𝓡).I) (s1 := s1)
    a (2 * Xn + 1) j hA hB hj (three_dvd_halfA p x) (C_mod3 p x) hC (xi_ne p x hz)
    rfl rfl ?_ (G_def p x) ?_ (I_def p x) ?_
  · rw [F_def, E2_def, E_def, E0_def, D_def, A_def]; ring
  · rw [H_def, Omega_def, E_def, E0_def, D_def, A_def, B1_def, hX]
    simp only [map_add, map_mul, map_one, map_ofNat]
    ring
  · rw [a1_def, D_def, A_def] at hs1
    linear_combination hs1

/-! ## The index of `K` -/

theorem Phalf_ne (hz : value p x = 0) : (𝓡).Phalf ≠ 0 := by
  intro h
  have hQ := Q_pos p x hz
  rw [Q_def, h] at hQ
  have hK := one_le_of_pos' (mul_self_pos' (guard p x hz).1)
  have e1 : ((0 : DiffRing V) * 0 - 1) * ((𝓡).K * (𝓡).K) + 1 = 1 - (𝓡).K * (𝓡).K := by ring
  rw [e1] at hQ
  linarith

theorem two_le_abs_Phalf (hz : value p x = 0) : 2 ≤ |(𝓡).Phalf| := by
  have hne := Phalf_ne p x hz
  have e : (𝓡).Phalf = 2 * ((𝓡).halfU * (𝓡).uv) := by rw [Phalf_def, U_def]; ring
  have hc : (𝓡).halfU * (𝓡).uv ≠ 0 := by
    intro h0
    exact hne (by rw [e, h0, mul_zero])
  rw [e, _root_.abs_mul, abs_two]
  linarith [one_le_abs hc]

/-- **The index of `K`**: `|K| = ψ_p(n)` for the base `p + 2 = |P/2|`. -/
theorem K_index (hz : value p x = 0) :
    ∃ pp n : V, |(𝓡).Phalf| = ι (pp + 2) ∧ |(𝓡).K| = ι (ycoord n pp) := by
  obtain ⟨P', hP'⟩ := abs_eq_ι (𝓡).Phalf
  have hP2 : 0 ≤ ι P' - (2 : DiffRing V) := by
    rw [← hP']
    linarith [two_le_abs_Phalf p x hz]
  obtain ⟨pp, hpp⟩ := nonneg_iff.mp hP2
  have hP : |(𝓡).Phalf| = ι pp + 2 := by
    rw [hP']
    linear_combination hpp
  obtain ⟨k, hk⟩ := abs_eq_ι (𝓡).K
  obtain ⟨β, q, d, e, -, -, -, -, -, hq, -, -⟩ := roots p x hz
  have e1 : (𝓡).Phalf * (𝓡).Phalf = (ι pp + 2) * (ι pp + 2) := by
    rw [← _root_.abs_mul_abs_self, hP]
  have e2 : (𝓡).K * (𝓡).K = ι k * ι k := by rw [← _root_.abs_mul_abs_self, hk]
  have hQ : ι q * ι q = ((ι pp + 2) * (ι pp + 2) - 1) * (ι k * ι k) + 1 := by
    rw [← hq, Q_def, e1, e2]
  have hpell : q * q = 1 + delta pp * k * k := by
    apply ι_injective (V := V)
    unfold delta
    simp only [map_add, map_mul, map_one, map_ofNat]
    linear_combination hQ
  obtain ⟨n, -, -, hy⟩ := ArithmeticPellClassification.solution_index pp q k hpell
  refine ⟨pp, n, ?_, by rw [hk, hy]⟩
  rw [hP]
  simp only [map_add, map_ofNat]

#print axioms C_index
#print axioms K_index

end DiophantineConsistency.Z10Index
