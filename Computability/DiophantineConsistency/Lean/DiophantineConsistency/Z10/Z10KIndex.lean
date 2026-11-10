import DiophantineConsistency.Z10.Z10Index
import DiophantineConsistency.ModelRatioBounds

/-! # The index of `K` in the ten-integer forms is `X + 1`

Package 106, integer lane (step S10 of the route). The signed counterpart of
`ModelRatio.ratio_K_index`.

* `K_index_eq` (plain variables): if `|P/2| = p + 2`, `|K| = ψ_p(n)`,
  `K = R + 1 + k₂ (P/2 - 1)` and `ψ_p(n) < 2 ψ_a(2R+1)` with `3R + 1 ≤ p` and
  `4 (a + 2) ≤ 2p + 3`, then `n = R + 1`. The congruence gives `n ≡ ±(R+1)` modulo
  `|P/2 - 1|` for either sign of `K` and of `P/2` (`Z10Cert.residue_pm`,
  `Z10Lucas.pm_trans`); the size bound gives `n ≤ 2R`.
* `indices`: at a zero with `X = ι Xn > 0`, both indices at once:
  `C = ψ_a(2X+1)` with `a + 2 = |A/2|` and `|K| = ψ_p(X+1)` with `p + 2 = |P/2|`. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.Z10KIndex
open Nine121 Nine121.N105Layout Z10Regs Z10Bootstrap Z10Squares Z10Guard Z10Index
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing ZRowsCoprimeSquares ArithmeticPellRecurrence
open ArithmeticPow ArithmeticHalfBinomialSandwich
open P138Bootstrap (one_le_of_pos' one_le_abs)

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## The generic statement -/

/-- The size half: an index `n ≥ 2R + 1` makes `ψ_p(n)` exceed `2 ψ_a(2R+1)`. -/
theorem index_small (R a pp n : V) (hR : 1 ≤ R) (hpA : 4 * (a + 2) ≤ 2 * pp + 3)
    (hKC : ycoord n pp < 2 * ycoord (2 * R + 1) a) : n < 2 * R + 1 := by
  by_contra hcon
  have hn : 2 * R + 1 ≤ n := not_lt.mp hcon
  have hX : 0 < power (2 * (a + 2)) (2 * R) :=
    power_pos _ _ (_root_.mul_pos (by simp) (ModelRatio.mr_pos_add_two a))
  have h2R : 2 ≤ power 2 R := by
    simpa only [power_one] using power_mono_exponent (2 : V) 1 R (by norm_num) hR
  have h4 : (4 : V) ≤ power 2 (2 * R) := by
    rw [two_mul R, power_add]
    calc (4 : V) = 2 * 2 := by norm_num
      _ ≤ power 2 R * power 2 R := mul_le_mul h2R h2R (by simp) (by simp)
  have hbig : 2 * ycoord (2 * R + 1) a < ycoord n pp := calc
    2 * ycoord (2 * R + 1) a ≤ 2 * power (2 * (a + 2)) (2 * R) :=
        mul_le_mul_of_nonneg_left (ycoord_le_power a (2 * R)) (by simp)
    _ < 4 * power (2 * (a + 2)) (2 * R) := mul_lt_mul_of_pos_right (by norm_num) hX
    _ ≤ power 2 (2 * R) * power (2 * (a + 2)) (2 * R) :=
        mul_le_mul_of_nonneg_right h4 (by simp)
    _ = power (4 * (a + 2)) (2 * R) := by
        rw [← power_mul_base, show (2 : V) * (2 * (a + 2)) = 4 * (a + 2) by ring]
    _ ≤ power (2 * pp + 3) (2 * R) := power_mono_base _ _ _ hpA
    _ ≤ ycoord (2 * R + 1) pp := power_le_ycoord pp (2 * R)
    _ ≤ ycoord n pp := (ordinate_strictMono pp).monotone hn
  exact absurd (lt_trans hKC hbig) (_root_.lt_irrefl _)

/-- **The index of `K`**, signed: the congruence `K ≡ R + 1 (mod P/2 - 1)` and the size
`|K| < 2 ψ_a(2R+1)` force the index `R + 1`. -/
theorem K_index_eq (R a pp n : V) {K Ph k2 : DiffRing V}
    (hR : 1 ≤ R) (hRp : 3 * R + 1 ≤ pp) (hpA : 4 * (a + 2) ≤ 2 * pp + 3)
    (hP : |Ph| = ι (pp + 2)) (hK : |K| = ι (ycoord n pp))
    (hK4 : K = ι R + 1 + k2 * (Ph - 1))
    (hKC : ycoord n pp < 2 * ycoord (2 * R + 1) a) : n = R + 1 := by
  have hn := index_small R a pp n hR hpA hKC
  have hnd : (ι n : DiffRing V) ≤ 2 * ι R := by
    have h0 := (ι_le_ι (V := V)).mpr (lt_iff_succ_le.mp hn)
    simp only [map_add, map_mul, map_one, map_ofNat] at h0
    linarith
  have hRd : (3 : DiffRing V) * ι R + 1 ≤ ι pp := by
    have h0 := (ι_le_ι (V := V)).mpr hRp
    simpa only [map_add, map_mul, map_one, map_ofNat] using h0
  have hR0 : (0 : DiffRing V) ≤ ι R := ι_nonneg R
  have hn0 : (0 : DiffRing V) ≤ ι n := ι_nonneg n
  -- the modulus `c = |P/2 - 1|`
  obtain ⟨c, hc⟩ := abs_eq_ι (Ph - 1)
  have hcd : (ι c : DiffRing V) ∣ Ph - 1 := by
    rw [← hc]
    exact (abs_dvd _ _).mpr dvd_rfl
  have hcs : (ι pp : DiffRing V) + 1 ≤ ι c := by
    have h1 := abs_sub_abs_le_abs_sub Ph 1
    rw [abs_one, hP, hc] at h1
    simp only [map_add, map_ofNat] at h1
    linarith
  have hc0 : 0 < c := by
    apply (ι_lt_ι (V := V)).mp
    rw [map_zero]
    linarith [ι_nonneg pp]
  -- `ψ_p(n) ≡ ±n`
  have hG : -Ph = ι (pp + 2) ∨ -Ph = -ι (pp + 2) := by
    rcases eq_or_eq_neg_abs Ph with h | h
    · right
      rw [← hP]
      linear_combination -h
    · left
      rw [← hP]
      linear_combination -h
  have hres := Z10Cert.residue_pm pp c n hc0 hG
    (by rw [show -Ph + 1 = -(Ph - 1) by ring]; exact (dvd_neg).mpr hcd)
  -- `ψ_p(n) ≡ ±(R + 1)`
  have hKd : (ι c : DiffRing V) ∣ K - (ι R + 1) :=
    hcd.trans (Dvd.intro k2 (by rw [hK4]; ring))
  have h2 : (ι c : DiffRing V) ∣ ι (ycoord n pp) - (ι R + 1) ∨
      (ι c : DiffRing V) ∣ ι (ycoord n pp) + (ι R + 1) := by
    rcases eq_or_eq_neg_abs K with h | h
    · left
      rw [← hK, ← h]
      exact hKd
    · right
      have e : |K| + (ι R + 1) = -(K - (ι R + 1)) := by linear_combination h
      rw [← hK, e]
      exact (dvd_neg).mpr hKd
  rcases Z10Lucas.pm_trans (Z10Lucas.pm_symm hres) h2 with h | h
  · have h0 := P138FirstIndex.eq_zero_of_dvd_small h (by
      rw [_root_.abs_lt]
      constructor <;> linarith)
    apply ι_injective (V := V)
    simp only [map_add, map_one]
    linear_combination h0
  · exfalso
    have h0 := P138FirstIndex.eq_zero_of_dvd_small h (by
      rw [_root_.abs_lt]
      constructor <;> linarith)
    linarith

/-! ## At the registers -/

variable (p : Fin 4 → DiffRing V) (x : Fin 10 → DiffRing V)
local notation "𝓡" => regs p x

theorem V_ne (hz : value p x = 0) : (𝓡).V ≠ 0 := by
  intro h0
  exact Phalf_ne p x hz (by rw [Phalf_def, uv_def, h0, mul_zero, mul_zero])

theorem abs_halfU (Xn : V) (hX : (𝓡).X = ι Xn) : |(𝓡).halfU| = |(𝓡).L| * ι Xn := by
  rw [halfU_def, hX, _root_.abs_mul, abs_of_nonneg (ι_nonneg Xn)]

theorem abs_Phalf : |(𝓡).Phalf| = 2 * |(𝓡).halfU| * (|(𝓡).halfU| * |(𝓡).V|) := by
  rw [Phalf_def, U_def, uv_def]
  simp only [_root_.abs_mul, abs_two]

theorem abs_halfA_le : |(𝓡).halfA| ≤ |(𝓡).halfU| * (1 + |(𝓡).V|) := by
  have h1V : |1 + (𝓡).V| ≤ 1 + |(𝓡).V| := by
    have h := abs_add_le (1 : DiffRing V) (𝓡).V
    rwa [abs_one] at h
  rw [halfA_eq, _root_.abs_mul]
  exact mul_le_mul_of_nonneg_left h1V (abs_nonneg _)

/-- **Both Pell indices**: at a zero with `X = ι Xn > 0`, `C = ψ_a(2X+1)` for
`a + 2 = |A/2|` and `|K| = ψ_p(X+1)` for `p + 2 = |P/2|`. -/
theorem indices (hz : value p x = 0) (Xn : V) (hX : (𝓡).X = ι Xn) (hX0 : 0 < Xn) :
    ∃ a pp : V, |(𝓡).halfA| = ι (a + 2) ∧ |(𝓡).Phalf| = ι (pp + 2) ∧
      2 * Xn + 1 < a + 2 ∧ (𝓡).C = ι (ycoord (2 * Xn + 1) a) ∧
      |(𝓡).K| = ι (ycoord (Xn + 1) pp) := by
  obtain ⟨a, hA, hB, hC⟩ := C_index p x hz Xn hX hX0
  obtain ⟨pp, n, hP, hK⟩ := K_index p x hz
  have hXd : (1 : DiffRing V) ≤ ι Xn := by
    have h := (ι_lt_ι (V := V)).mpr hX0
    rw [map_zero] at h
    exact one_le_of_pos' h
  have hL4 := abs_L_ge4 p x hz
  have hv1 := one_le_abs (V_ne p x hz)
  -- sizes: `m = |U/2| ≥ 4 X`, `m ≤ m |V|`, `4 m |V| ≤ m (m |V|)`
  have hm4X : 4 * ι Xn ≤ |(𝓡).halfU| := by
    rw [abs_halfU p x Xn hX]
    exact mul_le_mul_of_nonneg_right hL4 (ι_nonneg Xn)
  have hmv : |(𝓡).halfU| ≤ |(𝓡).halfU| * |(𝓡).V| :=
    le_mul_of_one_le_right (abs_nonneg _) hv1
  have hmmv : 4 * (|(𝓡).halfU| * |(𝓡).V|) ≤ |(𝓡).halfU| * (|(𝓡).halfU| * |(𝓡).V|) :=
    mul_le_mul_of_nonneg_right (by linarith)
      (_root_.mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hPe : (ι pp : DiffRing V) + 2 = 2 * |(𝓡).halfU| * (|(𝓡).halfU| * |(𝓡).V|) := by
    rw [← abs_Phalf p x, hP]
    simp only [map_add, map_ofNat]
  have hAe : (ι a : DiffRing V) + 2 ≤ |(𝓡).halfU| * (1 + |(𝓡).V|) := by
    have h := abs_halfA_le p x
    rw [hA] at h
    simpa only [map_add, map_ofNat] using h
  have hRp : 3 * Xn + 1 ≤ pp := by
    apply (ι_le_ι (V := V)).mp
    simp only [map_add, map_mul, map_one, map_ofNat]
    linarith
  have hpA : 4 * (a + 2) ≤ 2 * pp + 3 := by
    apply (ι_le_ι (V := V)).mp
    simp only [map_add, map_mul, map_ofNat]
    linarith
  have hKC : ycoord n pp < 2 * ycoord (2 * Xn + 1) a := by
    apply (ι_lt_ι (V := V)).mp
    simp only [map_mul, map_ofNat]
    have hCi := (C_interval p x hz).1
    rw [hK, hC, abs_of_nonneg (ι_nonneg (ycoord (2 * Xn + 1) a))] at hCi
    have h7 : (1 : DiffRing V) ≤ 2 * |(𝓡).L| - 1 := by linarith
    have h := mul_le_mul_of_nonneg_left h7 (ι_nonneg (ycoord n pp))
    linarith
  have hK4 : (𝓡).K = ι Xn + 1 + (𝓡).k2 * ((𝓡).Phalf - 1) := by
    have h := K_def p x
    rw [hX] at h
    exact h
  have hn := K_index_eq Xn a pp n (pos_iff_one_le.mp hX0) hRp hpA hP hK hK4 hKC
  rw [hn] at hK
  exact ⟨a, pp, hA, hP, hB, hC, hK⟩

#print axioms K_index_eq
#print axioms indices

end DiophantineConsistency.Z10KIndex
