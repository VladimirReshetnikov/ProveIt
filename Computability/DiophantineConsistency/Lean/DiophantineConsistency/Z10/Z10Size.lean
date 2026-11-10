import DiophantineConsistency.Z10.Z10KIndex

/-! # Crude sizes in the ten-integer forms

Package 106, integer lane (step S11 of the route). The positive-lane size lemmas
(`ModelRatio.ratio_lower`, `perturbation`) need the exact shape `a + 2 = M (U + 1)`; with a
signed `V` the factor is `|1 + V|`, which is `|V| + 1` or `|V| - 1`. The bound below only
uses `|1 + V| ≥ |V| - 1` and is enough for the exponential congruence.

* `crude_L`: with `a + 2 = M T`, `p + 2 = 2 M² (u + 4)`, `u + 3 ≤ T`, `M ≥ 1` and the upper
  guard `2 ψ_a(2R+1) < ψ_p(R+1) (2 Y + 1)`, one has `u ^ R ≤ Y`. Indeed
  `ψ_a(2R+1) ≥ (2a+3)^{2R} ≥ (2M(u+2))^{2R} ≥ (4M²(u+4))^R u^R ≥ ψ_p(R+1) u^R`.
* `crude`: with `M = Y R`, `u ^ R < a + 2`.
* `cube_lt`, `exp_cube_le`: `w³ < u ^ R` for `2 w ≤ u`, and `(2^{2R+1})³ ≤ u ^ R` for
  `u ≥ 128`, both for `R ≥ 3`.
* `threshold_ge`, `Y_ge64`: `Y ≥ 64` at a zero.
* `sizes`: at a zero with `X = ι Xn`, `Xn ≥ 3`: the indices of `Z10KIndex.indices`
  together with `|W| = ι Wn`, `Wn > 0`, `Wn³ < a + 2` and `(2^{2X+1})³ < a + 2`, where
  `a + 2 = |A/2|`. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.Z10Size
open Nine121 Nine121.N105Layout Z10Regs Z10Bootstrap Z10Squares Z10Guard Z10Index Z10KIndex
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing ZRowsCoprimeSquares ArithmeticPellRecurrence
open ArithmeticPow ArithmeticHalfBinomialSandwich
open P138Bootstrap (one_le_of_pos' one_le_abs)

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## The crude bound over plain variables -/

/-- The quotient is at least `u ^ R`, for either sign of `V` (`u = |V| - 4`, `T = |1 + V|`). -/
theorem crude_L (R Yl M T u a pp : V) (hM : 1 ≤ M)
    (ha : a + 2 = M * T) (hT : u + 3 ≤ T)
    (hp : pp + 2 = 2 * M * M * (u + 4))
    (hB3 : 2 * ycoord (2 * R + 1) a < ycoord (R + 1) pp * (2 * Yl + 1)) :
    power u R ≤ Yl := by
  have hbase : 2 * M * (u + 2) ≤ 2 * a + 3 := by
    apply (ι_le_ι (V := V)).mp
    have h1 := (ι_le_ι (V := V)).mpr (mul_le_mul_of_nonneg_left hT (by simp : (0 : V) ≤ M))
    have h2 : (ι (a + 2) : DiffRing V) = ι (M * T) := by rw [ha]
    have h3 := (ι_le_ι (V := V)).mpr hM
    simp only [map_add, map_mul, map_one, map_ofNat] at h1 h2 h3 ⊢
    linarith
  have hC : power (2 * M * (u + 2)) (2 * R) ≤ ycoord (2 * R + 1) a :=
    le_trans (power_mono_base _ _ _ hbase) (power_le_ycoord a (2 * R))
  have hK : ycoord (R + 1) pp ≤ power (4 * M * M * (u + 4)) R := by
    have h := ycoord_le_power pp R
    rwa [hp, show (2 : V) * (2 * M * M * (u + 4)) = 4 * M * M * (u + 4) by ring] at h
  have hsq : power (2 * M * (u + 2)) (2 * R) =
      power (2 * M * (u + 2) * (2 * M * (u + 2))) R := by
    rw [two_mul R, power_add, ← power_mul_base]
  have hprod : power (4 * M * M * (u + 4)) R * power u R ≤
      power (2 * M * (u + 2)) (2 * R) := by
    rw [hsq, ← power_mul_base]
    apply power_mono_base
    calc 4 * M * M * (u + 4) * u ≤ 4 * M * M * (u + 4) * u + 16 * M * M :=
          le_add_of_nonneg_right (by simp)
      _ = 2 * M * (u + 2) * (2 * M * (u + 2)) := by ring
  by_contra hcon
  have hlt : Yl + 1 ≤ power u R := lt_iff_succ_le.mp (not_le.mp hcon)
  have h1 : power (4 * M * M * (u + 4)) R * (2 * (Yl + 1)) ≤ 2 * ycoord (2 * R + 1) a := calc
    power (4 * M * M * (u + 4)) R * (2 * (Yl + 1)) ≤
        power (4 * M * M * (u + 4)) R * (2 * power u R) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlt (by simp)) (by simp)
    _ = 2 * (power (4 * M * M * (u + 4)) R * power u R) := by ring
    _ ≤ 2 * ycoord (2 * R + 1) a := mul_le_mul_of_nonneg_left (le_trans hprod hC) (by simp)
  have h21 : 2 * Yl + 1 ≤ 2 * (Yl + 1) := by
    rw [mul_add, mul_one]
    exact add_le_add (le_refl _) (by norm_num)
  have h2 : ycoord (R + 1) pp * (2 * Yl + 1) ≤
      power (4 * M * M * (u + 4)) R * (2 * (Yl + 1)) :=
    mul_le_mul hK h21 (by simp) (by simp)
  exact absurd (lt_of_lt_of_le (lt_of_le_of_lt h1 hB3) h2) (_root_.lt_irrefl _)

/-- The base `a + 2 = Y R T` exceeds `u ^ R`. -/
theorem crude (R Yl T u a pp : V) (hR : 1 ≤ R) (hYl : 1 ≤ Yl)
    (ha : a + 2 = Yl * R * T) (hT : u + 3 ≤ T)
    (hp : pp + 2 = 2 * (Yl * R) * (Yl * R) * (u + 4))
    (hB3 : 2 * ycoord (2 * R + 1) a < ycoord (R + 1) pp * (2 * Yl + 1)) :
    power u R < a + 2 := by
  have hM : 1 ≤ Yl * R := calc
    (1 : V) = 1 * 1 := (mul_one 1).symm
    _ ≤ Yl * R := mul_le_mul hYl hR (by simp) (by simp)
  have hL := crude_L R Yl (Yl * R) T u a pp hM ha hT hp hB3
  have h1 : Yl ≤ Yl * R := le_mul_of_one_le_right (by simp) hR
  have hT1 : 1 < T := lt_of_lt_of_le (lt_of_lt_of_le (by norm_num : (1 : V) < 3) le_add_self) hT
  have h2 : Yl * R < Yl * R * T := lt_mul_of_one_lt_right (pos_iff_one_le.mpr hM) hT1
  rw [ha]
  exact lt_of_le_of_lt (le_trans hL h1) h2

theorem cube_lt (u R Wn : V) (hR : 3 ≤ R) (hW : 0 < Wn) (hu : 2 * Wn ≤ u) :
    Wn * Wn * Wn < power u R := by
  have hu1 : 1 ≤ u :=
    le_trans (le_trans (pos_iff_one_le.mp hW) (le_mul_of_one_le_left (by simp) (by norm_num))) hu
  have h3 : power u 3 = u * u * u := by
    rw [show (3 : V) = 1 + 1 + 1 by norm_num, power_add, power_add, power_one]
  calc Wn * Wn * Wn < 8 * (Wn * Wn * Wn) :=
        lt_mul_of_one_lt_left (_root_.mul_pos (_root_.mul_pos hW hW) hW) (by norm_num)
    _ = 2 * Wn * (2 * Wn) * (2 * Wn) := by ring
    _ ≤ u * u * u := mul_le_mul (mul_le_mul hu hu (by simp) (by simp)) hu (by simp) (by simp)
    _ = power u 3 := h3.symm
    _ ≤ power u R := power_mono_exponent u 3 R hu1 hR

theorem exp_cube_le (u R : V) (hR : 3 ≤ R) (hu : 128 ≤ u) :
    Exp.exp (2 * R + 1) * Exp.exp (2 * R + 1) * Exp.exp (2 * R + 1) ≤ power u R := by
  have e1 : Exp.exp (2 * R + 1) * Exp.exp (2 * R + 1) * Exp.exp (2 * R + 1) =
      power 2 (2 * R + 1 + (2 * R + 1) + (2 * R + 1)) := by
    rw [power_add (2 : V) (2 * R + 1 + (2 * R + 1)) (2 * R + 1),
      power_add (2 : V) (2 * R + 1) (2 * R + 1), power_two]
  have e2 : power 2 (R + R + R + R + R + R + R) = power 128 R := by
    rw [show (128 : V) = 2 * 2 * 2 * 2 * 2 * 2 * 2 by norm_num]
    simp only [power_add, power_mul_base]
  have hexp : 2 * R + 1 + (2 * R + 1) + (2 * R + 1) ≤ R + R + R + R + R + R + R := calc
    2 * R + 1 + (2 * R + 1) + (2 * R + 1) = R + R + R + R + R + R + 3 := by ring
    _ ≤ R + R + R + R + R + R + R := add_le_add (le_refl _) hR
  rw [e1]
  calc power 2 (2 * R + 1 + (2 * R + 1) + (2 * R + 1))
      ≤ power 2 (R + R + R + R + R + R + R) := power_mono_exponent 2 _ _ (by norm_num) hexp
    _ = power 128 R := e2
    _ ≤ power u R := power_mono_base _ _ _ hu

/-! ## The registers -/

theorem threshold_ge : (16 : DiffRing V) ≤ ((threshold : ℤ) : DiffRing V) := by
  unfold threshold
  rw [Int.cast_pow]
  have h2 : ((2 : ℤ) : DiffRing V) = 2 := by norm_num
  rw [h2]
  calc (16 : DiffRing V) = 2 ^ 4 := by norm_num
    _ ≤ 2 ^ 34159017 := pow_le_pow_right₀ (by norm_num) (by norm_num)

variable (p : Fin 4 → DiffRing V) (x : Fin 10 → DiffRing V)
local notation "𝓡" => regs p x

theorem Y_ge64 (hz : value p x = 0) : 64 ≤ (𝓡).Y := by
  have hb := b_pos p x hz
  have hb4 := b_ge p x hz
  have hB : (1 : DiffRing V) ≤ Bc (𝓡).b ^ 2109 := one_le_of_pos' (pow_pos (Bc_pos hb) 2109)
  have h1 : (16 : DiffRing V) ≤ ((threshold : ℤ) : DiffRing V) * Bc (𝓡).b ^ 2109 := calc
    (16 : DiffRing V) = 16 * 1 := by norm_num
    _ ≤ ((threshold : ℤ) : DiffRing V) * Bc (𝓡).b ^ 2109 :=
        mul_le_mul threshold_ge hB (by norm_num) threshold_pos.le
  rw [Y_def]
  unfold Yc
  calc (64 : DiffRing V) = 4 * 16 := by norm_num
    _ ≤ (𝓡).b * (((threshold : ℤ) : DiffRing V) * Bc (𝓡).b ^ 2109) :=
        mul_le_mul hb4 h1 (by norm_num) hb.le

/-- **The crude sizes at a zero.** With `a + 2 = |A/2|`: the cube of `|W|` and the cube of
`2^{2X+1}` are below the base. -/
theorem sizes (hz : value p x = 0) (Xn : V) (hX : (𝓡).X = ι Xn) (hX3 : 3 ≤ Xn) :
    ∃ a pp Wn : V, |(𝓡).halfA| = ι (a + 2) ∧ |(𝓡).Phalf| = ι (pp + 2) ∧
      2 * Xn + 1 < a + 2 ∧ (𝓡).C = ι (ycoord (2 * Xn + 1) a) ∧
      |(𝓡).K| = ι (ycoord (Xn + 1) pp) ∧ |(𝓡).W| = ι Wn ∧ 0 < Wn ∧
      Wn * Wn * Wn < a + 2 ∧
      Exp.exp (2 * Xn + 1) * Exp.exp (2 * Xn + 1) * Exp.exp (2 * Xn + 1) < a + 2 := by
  have hX0 : 0 < Xn := lt_of_lt_of_le (by norm_num) hX3
  obtain ⟨a, pp, hA, hP, hB, hC, hK⟩ := indices p x hz Xn hX hX0
  obtain ⟨Yl, hYl⟩ := abs_eq_ι (𝓡).L
  obtain ⟨T, hT⟩ := abs_eq_ι (1 + (𝓡).V)
  obtain ⟨Un, hUn⟩ := abs_eq_ι (𝓡).V
  obtain ⟨Wn, hWn⟩ := abs_eq_ι (𝓡).W
  have hb := b_pos p x hz
  have hb4 := b_ge p x hz
  have hg := (guard p x hz).2.1
  have hY := Y_pos p x hz
  have hY64 := Y_ge64 p x hz
  -- `b ≤ g`
  have hx1 : 0 < x 1 := by
    by_contra hcon
    have h := _root_.mul_nonneg hb.le (neg_nonneg.mpr (not_lt.mp hcon))
    rw [mul_neg, ← g_def p x] at h
    linarith
  have hgb : (𝓡).b ≤ (𝓡).g := by
    have h := mul_le_mul_of_nonneg_left (one_le_of_pos' hx1) hb.le
    rw [mul_one, ← g_def p x] at h
    exact h
  -- `|V| ≥ 256 |W|` and `|W| ≥ 4`
  have hx5 : x 5 ≠ 0 := by
    intro h
    exact V_ne p x hz (by rw [V_def, h]; ring)
  have hx5a := one_le_abs hx5
  have eV : |(𝓡).V| = 4 * ((𝓡).g * (|x 5| * (𝓡).Y)) := by
    rw [V_def, _root_.abs_mul, _root_.abs_mul, _root_.abs_mul, abs_of_pos hY, abs_of_pos hg,
      abs_of_pos (by norm_num : (0 : DiffRing V) < 4)]
    ring
  have eW : |(𝓡).W| = (𝓡).b * |x 5| := by
    rw [W_def, _root_.abs_mul, abs_of_pos hb]
  have hW4 : 4 ≤ |(𝓡).W| := by
    rw [eW]
    calc (4 : DiffRing V) = 4 * 1 := by norm_num
      _ ≤ (𝓡).b * |x 5| := mul_le_mul hb4 hx5a (by norm_num) hb.le
  have hVW : 256 * |(𝓡).W| ≤ |(𝓡).V| := by
    rw [eV, eW]
    have h1 := mul_le_mul_of_nonneg_left hY64 (abs_nonneg (x 5))
    have h2 := mul_le_mul hgb h1 (_root_.mul_nonneg (abs_nonneg (x 5)) (by norm_num)) hg.le
    linarith
  have h1V : |(𝓡).V| ≤ |1 + (𝓡).V| + 1 := by
    have h := abs_add_le (1 + (𝓡).V) (-1)
    rwa [show 1 + (𝓡).V + -1 = (𝓡).V by ring, abs_neg, abs_one] at h
  -- the natural numbers `u = |V| - 4`, `T = |1 + V|`
  have hu0 : 0 ≤ ι Un - (4 : DiffRing V) := by
    rw [← hUn]
    linarith
  obtain ⟨u, hu⟩ := nonneg_iff.mp hu0
  have hu' : (ι Un : DiffRing V) = ι u + 4 := by linarith
  have hYl1 : 1 ≤ Yl := by
    apply (ι_le_ι (V := V)).mp
    rw [map_one]
    linarith [abs_L_ge4 p x hz]
  have hTu : u + 3 ≤ T := by
    apply (ι_le_ι (V := V)).mp
    simp only [map_add, map_ofNat]
    linarith
  have ha : a + 2 = Yl * Xn * T := by
    apply ι_injective (V := V)
    rw [← hA, abs_halfA p x Xn hX, hYl, hT]
    simp only [map_mul]
  have hp : pp + 2 = 2 * (Yl * Xn) * (Yl * Xn) * (u + 4) := by
    apply ι_injective (V := V)
    rw [← hP, abs_Phalf p x, abs_halfU p x Xn hX, hYl, hUn, hu']
    simp only [map_add, map_mul, map_ofNat]
    ring
  have hB3 : 2 * ycoord (2 * Xn + 1) a < ycoord (Xn + 1) pp * (2 * Yl + 1) := by
    have h := (C_interval p x hz).2
    rw [hK, hC, abs_of_nonneg (ι_nonneg (ycoord (2 * Xn + 1) a)), hYl] at h
    apply (ι_lt_ι (V := V)).mp
    simp only [map_add, map_mul, map_one, map_ofNat]
    exact h
  have hpow := crude Xn Yl T u a pp (le_trans (by norm_num) hX3) hYl1 ha hTu hp hB3
  have hu128 : 128 ≤ u := by
    apply (ι_le_ι (V := V)).mp
    simp only [map_ofNat]
    linarith
  have hu2W : 2 * Wn ≤ u := by
    apply (ι_le_ι (V := V)).mp
    simp only [map_mul, map_ofNat]
    linarith
  have hWn0 : 0 < Wn := by
    apply (ι_lt_ι (V := V)).mp
    rw [map_zero]
    linarith
  refine ⟨a, pp, Wn, hA, hP, hB, hC, hK, hWn, hWn0, ?_, ?_⟩
  · exact lt_trans (cube_lt u Xn Wn hX3 hWn0 hu2W) hpow
  · exact lt_of_le_of_lt (exp_cube_le u Xn hX3 hu128) hpow

#print axioms crude
#print axioms sizes

end DiophantineConsistency.Z10Size
