import GowersSzemeredi.Proofs16FamilyLemma6

/-! Comparing the polynomial integer-family width with the source's
exponentially small width. Padding the graph budget absorbs the polynomial
profile constants. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The printed recurrence denominator dominates the polynomial denominator
and its prefactor once the natural graph budget bounds the profile constants. -/
theorem family_printed_denominator_dominates {k C p q : Nat} (hk : 1 ≤ k)
    (hC : 1 ≤ C) (hCq : C ≤ q) (hpq : p ≤ q) :
    2 * familyRecDivisor k p q * (2 * (C * (q + 1)) + 1) ≤
      section16K k ^ (2 ^ (k + 1) * q) := by
  have hq : 1 ≤ q := hC.trans hCq
  have hCp : C ≤ 2 ^ q := hCq.trans (Nat.lt_two_pow_self.le)
  have hpp : p ≤ 2 ^ q := hpq.trans (Nat.lt_two_pow_self.le)
  have hq1 : q + 1 ≤ 2 ^ q := Nat.lt_two_pow_self
  have hb : 1 ≤ C * (q + 1) := hC.trans (Nat.le_mul_of_pos_right _ (by omega))
  have h12 : 12 ≤ (2 : Nat) ^ (4 * q) := by
    calc 12 ≤ 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (4 * q) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hproduct : C * p * (q + 1) ^ (2 * 2 ^ (k + 1) + 1) ≤
      (2 : Nat) ^ (q * (2 * 2 ^ (k + 1) + 3)) := by
    calc C * p * (q + 1) ^ (2 * 2 ^ (k + 1) + 1)
        ≤ (2 ^ q * 2 ^ q) * (2 ^ q) ^ (2 * 2 ^ (k + 1) + 1) :=
          Nat.mul_le_mul (Nat.mul_le_mul hCp hpp) (Nat.pow_le_pow_left hq1 _)
      _ = _ := by rw [← pow_add, ← pow_mul, ← pow_add]; congr 1; ring
  have hpoly : 2 * familyRecDivisor k p q * (2 * (C * (q + 1)) + 1) ≤
      12 * (C * p * (q + 1) ^ (2 * 2 ^ (k + 1) + 1)) := by
    have hlin : 2 * (C * (q + 1)) + 1 ≤ 3 * (C * (q + 1)) := by omega
    calc 2 * familyRecDivisor k p q * (2 * (C * (q + 1)) + 1)
        ≤ 2 * familyRecDivisor k p q * (3 * (C * (q + 1))) := Nat.mul_le_mul_left _ hlin
      _ = _ := by unfold familyRecDivisor; rw [pow_succ]; ring
  have he : 2 * 2 ^ (k + 1) + 7 ≤ (k + 4) * 2 ^ (k + 1) := by
    have h4 : 4 ≤ (2 : Nat) ^ (k + 1) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hprod := Nat.mul_le_mul (show 3 ≤ k + 2 by omega) h4
    nlinarith
  have hK : (2 : Nat) ^ (k + 4) ≤ section16K k := by
    unfold section16K
    exact Nat.le_mul_of_pos_left _ (by positivity)
  calc 2 * familyRecDivisor k p q * (2 * (C * (q + 1)) + 1)
      ≤ 12 * (C * p * (q + 1) ^ (2 * 2 ^ (k + 1) + 1)) := hpoly
    _ ≤ 2 ^ (4 * q) * 2 ^ (q * (2 * 2 ^ (k + 1) + 3)) := Nat.mul_le_mul h12 hproduct
    _ = 2 ^ (q * (2 * 2 ^ (k + 1) + 7)) := by rw [← pow_add]; congr 1; ring
    _ ≤ 2 ^ ((k + 4) * (2 ^ (k + 1) * q)) := by
      apply Nat.pow_le_pow_right (by norm_num)
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using Nat.mul_le_mul_left q he
    _ = (2 ^ (k + 4)) ^ (2 ^ (k + 1) * q) := by rw [pow_mul]
    _ ≤ section16K k ^ (2 ^ (k + 1) * q) := Nat.pow_le_pow_left hK _

/-- An exponential-denominator width is dominated either by a singleton
or by the polynomial width, including at every finite input scale. -/
theorem source_width_le_max_polynomial (m b E R : Nat) (hb : 0 < b) (hE : 0 < E)
    (hR : 0 < R) (hbudget : 2 * E * (2 * b + 1) ≤ R)
    {a zeta : Real} (ha : 0 < a) (hz : 0 < zeta) (hzOne : zeta ≤ 1) :
    zeta / 2 * (m : Real) ^ (a / (2 * (R : Real))) ≤
      max 1 (zeta / (4 * (b : Real)) * (m : Real) ^ (a / (4 * (E : Real)))) := by
  have hbR : (0 : Real) < b := by exact_mod_cast hb
  have hER : (0 : Real) < E := by exact_mod_cast hE
  have hRR : (0 : Real) < R := by exact_mod_cast hR
  by_cases hm : m = 0
  · subst m
    rw [Nat.cast_zero, Real.zero_rpow (div_pos ha (by positivity : 0 < 2 * (R : Real))).ne', mul_zero]
    exact le_max_of_le_left (by norm_num)
  have hm0 : (0 : Real) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hm1 : (1 : Real) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm
  let u : Real := (m : Real) ^ (a / (2 * (R : Real)))
  have hu0 : 0 < u := Real.rpow_pos_of_pos hm0 _
  by_cases hsmall : zeta / 2 * u ≤ 1
  · exact hsmall.trans (le_max_left _ _)
  have hu2 : 2 ≤ u := by
    have hzmul := mul_le_mul_of_nonneg_right hzOne hu0.le
    have hlarge : 1 < zeta / 2 * u := lt_of_not_ge hsmall
    nlinarith
  have hpower : 2 * (b : Real) ≤ u ^ (2 * b) := by
    have hnat : (2 * b : Nat) ≤ 2 ^ (2 * b) := Nat.lt_two_pow_self.le
    have hreal : 2 * (b : Real) ≤ (2 : Real) ^ (2 * b) := by exact_mod_cast hnat
    exact hreal.trans (pow_le_pow_left₀ (by norm_num) hu2 _)
  have hbudgetR : 2 * (E : Real) * (2 * (b : Real) + 1) ≤ R := by exact_mod_cast hbudget
  have hexp : a / (2 * (R : Real)) * ((2 * b + 1 : Nat) : Real) ≤ a / (4 * (E : Real)) := by
    rw [div_mul_eq_mul_div]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    push_cast
    have h := mul_le_mul_of_nonneg_left hbudgetR ha.le
    nlinarith
  have hcost : u ^ (2 * b + 1) ≤ (m : Real) ^ (a / (4 * (E : Real))) := by
    calc u ^ (2 * b + 1) = (m : Real) ^
          (a / (2 * (R : Real)) * ((2 * b + 1 : Nat) : Real)) := by
            dsimp [u]
            rw [Real.rpow_mul hm0.le, Real.rpow_natCast]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hm1 hexp
  have hcost' : 2 * (b : Real) * u ≤ (m : Real) ^ (a / (4 * (E : Real))) := by
    refine (mul_le_mul_of_nonneg_right hpower hu0.le).trans ?_
    simpa only [pow_succ] using hcost
  calc zeta / 2 * (m : Real) ^ (a / (2 * (R : Real)))
      = zeta / (4 * (b : Real)) * (2 * (b : Real) * u) := by
          dsimp [u]
          field_simp [hbR.ne']
          ring
    _ ≤ zeta / (4 * (b : Real)) * (m : Real) ^ (a / (4 * (E : Real))) :=
      mul_le_mul_of_nonneg_left hcost' (by positivity)
    _ ≤ _ := le_max_right _ _

/-- The literal recurrence width from Lemma 16.6 follows from a polynomial
integer cover, or a singleton cover, with the same padded graph budget. -/
theorem family_printed_width_le_max (m : Nat) {k C p q : Nat} (hk : 1 ≤ k)
    (hC : 1 ≤ C) (hp : 0 < p) (hCq : C ≤ q) (hpq : p ≤ q)
    {a zeta : Real} (ha : 0 < a) (hz : 0 < zeta) (hzOne : zeta ≤ 1) :
    zeta / 2 * (m : Real) ^ (a / (2 * (section16K k : Real) ^ (2 ^ (k + 1) * q))) ≤
      max 1 (section16PowerWidth (familyWidthPrefactor C) (familyWidthDivisor k p) m q a zeta) := by
  have hb : 0 < C * (q + 1) := Nat.mul_pos (by omega) (by omega)
  have hE : 0 < familyRecDivisor k p q := by unfold familyRecDivisor; positivity
  have hR : 0 < section16K k ^ (2 ^ (k + 1) * q) := by unfold section16K; positivity
  have h := source_width_le_max_polynomial m (C * (q + 1)) (familyRecDivisor k p q)
    (section16K k ^ (2 ^ (k + 1) * q)) hb hE hR
    (family_printed_denominator_dominates hk hC hCq hpq) ha hz hzOne
  simpa only [section16PowerWidth, familyWidthPrefactor, familyWidthDivisor,
    familyRecDivisor, Nat.cast_pow] using h

/-- Integer cell widths absorb the singleton alternative in the comparison,
so the printed width follows at every input scale, including zero. -/
theorem family_printed_width_le_of_power_width (m w : Nat) {k C p q : Nat}
    (hk : 1 ≤ k) (hC : 1 ≤ C) (hp : 0 < p) (hCq : C ≤ q) (hpq : p ≤ q)
    {a zeta : Real} (ha : 0 < a) (hz : 0 < zeta) (hzOne : zeta ≤ 1)
    (hw : section16PowerWidth (familyWidthPrefactor C) (familyWidthDivisor k p) m q a zeta ≤ w) :
    zeta / 2 * (m : Real) ^ (a / (2 * (section16K k : Real) ^ (2 ^ (k + 1) * q))) ≤ w := by
  have hK : (0 : Real) < section16K k := by unfold section16K; positivity
  by_cases hm : m = 0
  · subst m
    rw [Nat.cast_zero, Real.zero_rpow (div_pos ha (by positivity)).ne', mul_zero]
    exact Nat.cast_nonneg _
  have hm0 : (0 : Real) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hC0 : 0 < C := by omega
  have hW : 0 < section16PowerWidth (familyWidthPrefactor C) (familyWidthDivisor k p) m q a zeta := by
    unfold section16PowerWidth familyWidthPrefactor familyWidthDivisor
    positivity
  have hw0 : (0 : Real) < w := hW.trans_le hw
  have hwn : 0 < w := by exact_mod_cast hw0
  have hw1 : (1 : Real) ≤ w := by exact_mod_cast hwn
  exact (family_printed_width_le_max m hk hC hp hCq hpq ha hz hzOne).trans (max_le hw1 hw)

end LeanProofs.GowersSzemeredi
