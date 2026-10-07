import GowersSzemeredi.Proofs13UniformDensityParameters

/-! Ceiling budgets with a threshold uniform over variable exponents. -/

set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Filter

/-- A factor-two exponent margin permits a threshold depending only on lower
bounds for the target coefficient, target exponent, and Bohr radius. -/
theorem uniform_rounded_power_budgets
    {c₀ d z₀ e₀ : Real} (hc₀ : 0 < c₀) (hd : 0 < d) (hdone : d ≤ 1)
    (hz₀ : 0 < z₀) (he₀ : 0 < e₀) :
    ∃ N₀ : Nat, ∀ N : Nat, N₀ ≤ N → ∀ c e u v w z P Q : Real,
      c₀ ≤ c → c ≤ 1 / 2 → e₀ ≤ e → 2 * e ≤ 1 →
      0 < v → v ≤ 1 → 0 < w → w ≤ 1 → z₀ ≤ z →
      2 * e ≤ u * v → 2 * e ≤ u * w →
      d * (N : Real) ^ u ≤ P → P ^ v / 2 ≤ Q →
      ∃ m : Nat, 0 < m ∧ m ^ 2 ≤ N ∧ (m : Real) + 1 ≤ Q ∧
        c * (N : Real) ^ e ≤ m ∧ P ^ (-w) ≤ z / m := by
  have ht := eventually_nat_mul_rpow_le (C := 1) (D := c₀) he₀ hc₀
  have hr := eventually_nat_mul_rpow_le (C := 4) (D := d) he₀ hd
  have hb := eventually_nat_mul_rpow_le (C := 1) (D := z₀ * d) he₀ (mul_pos hz₀ hd)
  have hall : ∀ᶠ N : Nat in atTop, ∀ c e u v w z P Q : Real,
      c₀ ≤ c → c ≤ 1 / 2 → e₀ ≤ e → 2 * e ≤ 1 →
      0 < v → v ≤ 1 → 0 < w → w ≤ 1 → z₀ ≤ z →
      2 * e ≤ u * v → 2 * e ≤ u * w →
      d * (N : Real) ^ u ≤ P → P ^ v / 2 ≤ Q →
      ∃ m : Nat, 0 < m ∧ m ^ 2 ≤ N ∧ (m : Real) + 1 ≤ Q ∧
        c * (N : Real) ^ e ≤ m ∧ P ^ (-w) ≤ z / m := by
    filter_upwards [ht, hr, hb, eventually_ge_atTop (1 : Nat)] with N ht hr hb hN
    intro c e u v w z P Q hc hcmax he hemax hv hvone hw hwone hz hrec hbohr hP hQ
    have hNreal : (1 : Real) ≤ N := by exact_mod_cast hN
    have hNpos : (0 : Real) < N := zero_lt_one.trans_le hNreal
    have hcpos : 0 < c := hc₀.trans_le hc
    have hepos : 0 < e := he₀.trans_le he
    have hpower : (N : Real) ^ e₀ ≤ (N : Real) ^ e :=
      Real.rpow_le_rpow_of_exponent_le hNreal he
    have hone : 1 ≤ c * (N : Real) ^ e := by
      calc
        _ ≤ c₀ * (N : Real) ^ e₀ := by simpa only [Real.rpow_zero, mul_one] using ht
        _ ≤ _ := mul_le_mul hc hpower (Real.rpow_nonneg hNpos.le _) hcpos.le
    have hrecconst : 4 ≤ d * (N : Real) ^ e := by
      calc
        _ ≤ d * (N : Real) ^ e₀ := by simpa only [Real.rpow_zero, mul_one] using hr
        _ ≤ _ := mul_le_mul_of_nonneg_left hpower hd.le
    have hbohrconst : 1 ≤ z * d * (N : Real) ^ e := by
      calc
        _ ≤ z₀ * d * (N : Real) ^ e₀ := by simpa only [Real.rpow_zero, mul_one] using hb
        _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_right hz hd.le) hpower
          (Real.rpow_nonneg hNpos.le _) (mul_nonneg (hz₀.trans_le hz).le hd.le)
    have hPpos : 0 < P := (mul_pos hd (Real.rpow_pos_of_pos hNpos u)).trans_le hP
    have hpow (s : Real) (hs : 0 < s) (hsone : s ≤ 1) (hgap : 2 * e ≤ u * s) :
        d * ((N : Real) ^ e * (N : Real) ^ e) ≤ P ^ s := by
      calc
        _ = d * (N : Real) ^ (2 * e) := by rw [← Real.rpow_add hNpos]; congr 2; ring
        _ ≤ d ^ s * (N : Real) ^ (u * s) := by
          apply mul_le_mul _ (Real.rpow_le_rpow_of_exponent_le hNreal hgap)
            (Real.rpow_nonneg hNpos.le _) (Real.rpow_nonneg hd.le _)
          simpa only [Real.rpow_one] using
            Real.rpow_le_rpow_of_exponent_ge hd hdone hsone
        _ = (d * (N : Real) ^ u) ^ s := by
          rw [Real.mul_rpow hd.le (Real.rpow_nonneg hNpos.le _), ← Real.rpow_mul hNpos.le]
        _ ≤ P ^ s := Real.rpow_le_rpow (by positivity) hP hs.le
    let m : Nat := Nat.ceil (c * (N : Real) ^ e)
    have hmpos : 0 < m := Nat.one_le_ceil_iff.mpr (zero_lt_one.trans_le hone)
    have hmlower : c * (N : Real) ^ e ≤ (m : Real) := Nat.le_ceil _
    have hmround : (m : Real) < c * (N : Real) ^ e + 1 :=
      Nat.ceil_lt_add_one (zero_le_one.trans hone)
    have hmupper : (m : Real) ≤ (N : Real) ^ e := by
      have hmul := mul_le_mul_of_nonneg_right hcmax (Real.rpow_nonneg hNpos.le e)
      linarith only [hmround, hone, hmul]
    have hnone : 1 ≤ (N : Real) ^ e := Real.one_le_rpow hNreal hepos.le
    have hmsquare : (m : Real) ^ 2 ≤ (N : Real) := by
      calc
        _ ≤ ((N : Real) ^ e) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hmupper 2
        _ = (N : Real) ^ (2 * e) := by rw [← Real.rpow_mul_natCast hNpos.le]; congr 1; ring
        _ ≤ (N : Real) ^ (1 : Real) := Real.rpow_le_rpow_of_exponent_le hNreal hemax
        _ = _ := Real.rpow_one _
    refine ⟨m, hmpos, by exact_mod_cast hmsquare, ?_, hmlower, ?_⟩
    · have hmul := mul_le_mul_of_nonneg_right hrecconst (Real.rpow_nonneg hNpos.le e)
      have hp := hpow v hv hvone hrec
      nlinarith only [hmupper, hnone, hmul, hp, hQ]
    · have hmul := mul_le_mul_of_nonneg_right hbohrconst (Real.rpow_nonneg hNpos.le e)
      have hp := mul_le_mul_of_nonneg_left (hpow w hw hwone hbohr) (hz₀.trans_le hz).le
      have hmP : (m : Real) ≤ z * P ^ w := by nlinarith only [hmupper, hmul, hp]
      rw [Real.rpow_neg hPpos.le, ← one_div]
      apply (div_le_div_iff₀ (Real.rpow_pos_of_pos hPpos _) (by exact_mod_cast hmpos)).mpr
      simpa only [one_mul] using hmP
  exact eventually_atTop.mp hall

end LeanProofs.GowersSzemeredi
