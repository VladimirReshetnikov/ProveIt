import GowersSzemeredi.Proofs18LengthSixRoute

/-! Power lower bounds for the single-piece width pipeline.

The scale conditions of the single-piece route ask that certain nested
widths exceed fixed targets. Every width in the pipeline is a power of the
input above an explicit threshold:
* `coverWidth E t L = ⌈L^E⌉` is at least `L^E`;
* one unused-coordinate step `liftLastW w t L = √(w(t/2)⌈L/8⌉ − 1) − 1` turns
  `L^a` into `L^(a/4)`, above `max(8L₀ + 8, 6^(4/a))`.

The thresholds are `exp(O(1/a))`, so their logarithms are polynomial in
`1/a`, which is what the final budget needs.
* `WidthPowerLB`, `coverWidth_powerLB`, `liftLastW_powerLB`,
  `WidthPowerLB.min`, `WidthPowerLB.mono_exponent`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- `w L ≥ L^a` for every `L ≥ L₀`. -/
def WidthPowerLB (w : Nat → Nat) (a L0 : Real) : Prop :=
  ∀ L : Nat, L0 ≤ L → (L : Real) ^ a ≤ w L

theorem WidthPowerLB.mono_threshold {w : Nat → Nat} {a L0 L1 : Real}
    (h : WidthPowerLB w a L0) (hL : L0 ≤ L1) : WidthPowerLB w a L1 :=
  fun L hL1 => h L (hL.trans hL1)

/-- A smaller exponent, above threshold one. -/
theorem WidthPowerLB.mono_exponent {w : Nat → Nat} {a b L0 : Real}
    (h : WidthPowerLB w a L0) (hb : b ≤ a) (hL0 : 1 ≤ L0) : WidthPowerLB w b L0 := by
  intro L hL
  have h1 : (1 : Real) ≤ L := hL0.trans hL
  exact (Real.rpow_le_rpow_of_exponent_le h1 hb).trans (h L hL)

theorem WidthPowerLB.min {w v : Nat → Nat} {a b L0 L1 : Real}
    (hw : WidthPowerLB w a L0) (hv : WidthPowerLB v b L1) (hL0 : 1 ≤ L0) :
    WidthPowerLB (fun L => min (w L) (v L)) (min a b) (max L0 L1) := by
  intro L hL
  have hL0' : L0 ≤ L := (le_max_left _ _).trans hL
  have hL1' : L1 ≤ L := (le_max_right _ _).trans hL
  have h1 : (1 : Real) ≤ L := hL0.trans hL0'
  have ha := (Real.rpow_le_rpow_of_exponent_le h1 (min_le_left a b)).trans (hw L hL0')
  have hb := (Real.rpow_le_rpow_of_exponent_le h1 (min_le_right a b)).trans (hv L hL1')
  show (L : Real) ^ (Min.min a b) ≤ ((Min.min (w L) (v L) : Nat) : Real)
  rw [Nat.cast_min]
  exact le_min ha hb

theorem coverWidth_powerLB (E : Real → Real) (t : Real) (hE : 0 ≤ E (t / 2)) :
    WidthPowerLB (coverWidth E t) (E (t / 2)) 0 := by
  intro L _
  unfold coverWidth
  rw [max_eq_right hE]
  exact Nat.le_ceil _

/-- The key estimate: `√(n − 1) − 1 ≥ x` when `n ≥ x⁴/8` and `x ≥ 6`. -/
theorem nat_sqrt_pred_pred_ge {n : Nat} {x : Real} (hx : 6 ≤ x)
    (hn : x ^ 4 / 8 ≤ n) : x ≤ ((Nat.sqrt (n - 1) - 1 : Nat) : Real) := by
  set k := ⌈x⌉₊ with hk
  have hxk : x ≤ k := Nat.le_ceil x
  have hk2 : (k : Real) ≤ x + 1 := (Nat.ceil_lt_add_one (by linarith)).le
  have hx2 : 36 ≤ x ^ 2 := by nlinarith
  have hx4' : 36 * x ^ 2 ≤ x ^ 4 := by nlinarith
  have hn1 : 1 ≤ n := by
    have : (1 : Real) ≤ n := by nlinarith
    exact_mod_cast this
  have hsq : (k + 1) ^ 2 ≤ n - 1 := by
    have hreal : ((k + 1 : Nat) : Real) ^ 2 ≤ (n : Real) - 1 := by
      push_cast
      have hk0 : (0 : Real) ≤ (k : Real) + 1 := by positivity
      have hkx : ((k : Real) + 1) ^ 2 ≤ (x + 2) ^ 2 :=
        pow_le_pow_left₀ hk0 (by linarith) 2
      nlinarith
    have : ((k + 1) ^ 2 : Nat) ≤ ((n - 1 : Nat) : Real) := by
      push_cast [Nat.cast_sub hn1]
      exact_mod_cast hreal
    exact_mod_cast this
  have hroot : k + 1 ≤ Nat.sqrt (n - 1) := Nat.le_sqrt.mpr (by nlinarith [hsq])
  have hfinal : k ≤ Nat.sqrt (n - 1) - 1 := by omega
  exact hxk.trans (by exact_mod_cast hfinal)

/-- **One unused-coordinate step**: `L^a` becomes `L^(a/4)`. -/
theorem liftLastW_powerLB {w : Real → Nat → Nat} {t a L0 : Real} (ha : 0 < a) (ha1 : a ≤ 1)
    (hL00 : 0 ≤ L0) (h : WidthPowerLB (w (t / 2)) a L0) :
    WidthPowerLB (liftLastW w t) (a / 4) (max (8 * L0 + 8) ((6 : Real) ^ (4 / a))) := by
  intro L hL
  have hL8 : 8 * L0 + 8 ≤ (L : Real) := (le_max_left _ _).trans hL
  have hL6 : (6 : Real) ^ (4 / a) ≤ L := (le_max_right _ _).trans hL
  have hLpos : (0 : Real) < L := by linarith
  have hL4 : 4 ≤ L := by
    have : (4 : Real) ≤ L := by linarith
    exact_mod_cast this
  unfold liftLastW
  rw [if_pos hL4]
  -- the inner width
  set L' := ⌈(L : Real) / 8⌉₊ with hL'
  have hL'ge : (L : Real) / 8 ≤ L' := Nat.le_ceil _
  have hL'0 : L0 ≤ (L' : Real) := by linarith
  have hw := h L' hL'0
  have hpow8 : ((L : Real) / 8) ^ a ≤ (L' : Real) ^ a :=
    Real.rpow_le_rpow (by positivity) hL'ge ha.le
  -- the power x = L^(a/4)
  set x := (L : Real) ^ (a / 4) with hx
  have hx6 : 6 ≤ x := by
    have h1 : ((6 : Real) ^ (4 / a)) ^ (a / 4) ≤ (L : Real) ^ (a / 4) :=
      Real.rpow_le_rpow (by positivity) hL6 (by positivity)
    rw [← Real.rpow_mul (by norm_num), show 4 / a * (a / 4) = 1 by field_simp,
      Real.rpow_one] at h1
    exact h1
  have hx4 : x ^ 4 = (L : Real) ^ a := by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul hLpos.le]
    congr 1
    push_cast
    ring
  have h8a : (8 : Real) ^ a ≤ 8 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : Real) ≤ 8) ha1
  have hdiv : (L : Real) ^ a / 8 ≤ ((L : Real) / 8) ^ a := by
    rw [Real.div_rpow hLpos.le (by norm_num)]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) h8a
  have hn : x ^ 4 / 8 ≤ (w (t / 2) L' : Real) := by
    rw [hx4]
    exact hdiv.trans (hpow8.trans hw)
  exact nat_sqrt_pred_pred_ge hx6 hn


/-- **Composition**: powers multiply above the pulled-back threshold. -/
theorem WidthPowerLB.comp {w v : Nat → Nat} {a b L0 L1 : Real}
    (hw : WidthPowerLB w a L0) (hv : WidthPowerLB v b L1) (ha : 0 < a) (hb : 0 ≤ b)
    (hL0 : 1 ≤ L0) (hL1 : 0 ≤ L1) :
    WidthPowerLB (fun L => v (w L)) (a * b) (max L0 (L1 ^ (1 / a))) := by
  intro L hL
  have hL0' : L0 ≤ L := (le_max_left _ _).trans hL
  have hL1' : L1 ^ (1 / a) ≤ L := (le_max_right _ _).trans hL
  have hLpos : (0 : Real) ≤ L := by linarith
  have hwL := hw L hL0'
  have hLa : L1 ≤ (L : Real) ^ a := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg hL1 _) hL1' ha.le
    rwa [← Real.rpow_mul hL1, show 1 / a * a = 1 by field_simp, Real.rpow_one] at h
  have hvw := hv (w L) (hLa.trans hwL)
  calc (L : Real) ^ (a * b) = ((L : Real) ^ a) ^ b := Real.rpow_mul hLpos a b
    _ ≤ (w L : Real) ^ b := Real.rpow_le_rpow (Real.rpow_nonneg hLpos _) hwL hb
    _ ≤ _ := hvw

/-- One lift of a cover width. -/
theorem liftLastW_coverWidth_powerLB {E : Real → Real} {t : Real}
    (hE : 0 < E (t / 2 / 2)) (hE1 : E (t / 2 / 2) ≤ 1) :
    WidthPowerLB (liftLastW (coverWidth E) t) (E (t / 2 / 2) / 4)
      (max (8 * 0 + 8) ((6 : Real) ^ (4 / E (t / 2 / 2)))) :=
  liftLastW_powerLB hE hE1 le_rfl (coverWidth_powerLB E (t / 2) hE.le)

/-- Two lifts of a cover width. -/
theorem liftLastW_two_coverWidth_powerLB {E : Real → Real} {t : Real}
    (hE : 0 < E (t / 2 / 2 / 2)) (hE1 : E (t / 2 / 2 / 2) ≤ 1) :
    WidthPowerLB ((liftLastW^[2] (coverWidth E)) t) (E (t / 2 / 2 / 2) / 4 / 4)
      (max (8 * max (8 * 0 + 8) ((6 : Real) ^ (4 / E (t / 2 / 2 / 2))) + 8)
        ((6 : Real) ^ (4 / (E (t / 2 / 2 / 2) / 4)))) := by
  have h1 := liftLastW_coverWidth_powerLB (E := E) (t := t / 2) hE hE1
  have hrw : (liftLastW^[2] (coverWidth E)) t = liftLastW (liftLastW (coverWidth E)) t := by
    rfl
  rw [hrw]
  exact liftLastW_powerLB (by positivity) (by linarith) (by positivity) h1

theorem section16CappedWidthExponent_le_one (e T : Real) :
    section16CappedWidthExponent e T ≤ 1 := by
  unfold section16CappedWidthExponent
  refine (min_le_right _ _).trans ?_
  have hM : (1 : Real) < max 2 T := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hlog := Real.log_pos hM
  rw [div_le_one hlog]
  exact Real.log_le_log (by norm_num) (le_max_left _ _)

theorem sixEb_le_one {A Bq : Nat → Real} (l : Nat) (g t s : Real) (hs : 0 < s) (hs1 : s ≤ 1) :
    sixEb A Bq l g t s ≤ 1 := by
  unfold sixEb
  split_ifs
  · exact cubicBaseExponent_le_one (section16BaseFamilyBound_pos g t) hs hs1
  · exact section16CappedWidthExponent_le_one _ _

/-- The exponent of `sixW` at `t`. -/
def sixWExp (Eb : Nat → Real → Real → Real → Real) (alpha t : Real) : Real :=
  min (Eb 1 (alpha / 2) (globalBudget alpha (alpha / 2) 2) (t / 2 / 2 / 2) / 4 / 4)
    (Eb 2 (alpha / 2) (globalBudget alpha (alpha / 2) 2) (t / 2 / 2) / 4)

/-- The threshold of `sixW` at `t`. -/
def sixWThr (Eb : Nat → Real → Real → Real → Real) (alpha t : Real) : Real :=
  let E1 := Eb 1 (alpha / 2) (globalBudget alpha (alpha / 2) 2) (t / 2 / 2 / 2)
  let E2 := Eb 2 (alpha / 2) (globalBudget alpha (alpha / 2) 2) (t / 2 / 2)
  max (max (8 * max (8 * 0 + 8) ((6 : Real) ^ (4 / E1)) + 8) ((6 : Real) ^ (4 / (E1 / 4))))
    (max (8 * 0 + 8) ((6 : Real) ^ (4 / E2)))

theorem one_le_sixWThr (Eb : Nat → Real → Real → Real → Real) (alpha t : Real) :
    1 ≤ sixWThr Eb alpha t := by
  unfold sixWThr
  refine le_trans ?_ (le_max_left _ _)
  refine le_trans ?_ (le_max_left _ _)
  have : (8 : Real) ≤ max (8 * 0 + 8) ((6 : Real) ^ (4 / Eb 1 (alpha / 2)
    (globalBudget alpha (alpha / 2) 2) (t / 2 / 2 / 2))) := by
    refine le_trans ?_ (le_max_left _ _); norm_num
  linarith

/-- **The width `sixW` is a power above an explicit threshold.** -/
theorem sixW_powerLB {Eb : Nat → Real → Real → Real → Real} {alpha t : Real}
    (hE : ∀ l g u s, 0 < s → s ≤ 1 → 0 < Eb l g u s ∧ Eb l g u s ≤ 1)
    (ht : 0 < t) (ht1 : t ≤ 1) :
    WidthPowerLB (sixW Eb alpha t) (sixWExp Eb alpha t) (sixWThr Eb alpha t) := by
  have hs8 : 0 < t / 2 / 2 / 2 := by positivity
  have hs81 : t / 2 / 2 / 2 ≤ 1 := by linarith
  have hs4 : 0 < t / 2 / 2 := by positivity
  have hs41 : t / 2 / 2 ≤ 1 := by linarith
  obtain ⟨h1, h1'⟩ := hE 1 (alpha / 2) (globalBudget alpha (alpha / 2) 2) _ hs8 hs81
  obtain ⟨h2, h2'⟩ := hE 2 (alpha / 2) (globalBudget alpha (alpha / 2) 2) _ hs4 hs41
  have hA := liftLastW_two_coverWidth_powerLB
    (E := Eb 1 (alpha / 2) (globalBudget alpha (alpha / 2) 2)) (t := t) h1 h1'
  have hB := liftLastW_coverWidth_powerLB
    (E := Eb 2 (alpha / 2) (globalBudget alpha (alpha / 2) 2)) (t := t) h2 h2'
  have hA1 : (1 : Real) ≤ max (8 * max (8 * 0 + 8) ((6 : Real) ^ (4 / Eb 1 (alpha / 2)
      (globalBudget alpha (alpha / 2) 2) (t / 2 / 2 / 2))) + 8)
      ((6 : Real) ^ (4 / (Eb 1 (alpha / 2) (globalBudget alpha (alpha / 2) 2)
        (t / 2 / 2 / 2) / 4))) := by
    refine le_trans ?_ (le_max_left _ _)
    have : (8 : Real) ≤ max (8 * 0 + 8) ((6 : Real) ^ (4 / Eb 1 (alpha / 2)
      (globalBudget alpha (alpha / 2) 2) (t / 2 / 2 / 2))) := by
      refine le_trans ?_ (le_max_left _ _); norm_num
    linarith
  have h := WidthPowerLB.min hA hB hA1
  intro L hL
  have hL' := h L hL
  simpa only [sixW, sixWExp, Function.iterate_one] using hL'

theorem sixWExp_pos {Eb : Nat → Real → Real → Real → Real} {alpha t : Real}
    (hE : ∀ l g u s, 0 < s → s ≤ 1 → 0 < Eb l g u s ∧ Eb l g u s ≤ 1)
    (ht : 0 < t) (ht1 : t ≤ 1) : 0 < sixWExp Eb alpha t := by
  have h1 := (hE 1 (alpha / 2) (globalBudget alpha (alpha / 2) 2) (t / 2 / 2 / 2)
    (by positivity) (by linarith)).1
  have h2 := (hE 2 (alpha / 2) (globalBudget alpha (alpha / 2) 2) (t / 2 / 2)
    (by positivity) (by linarith)).1
  unfold sixWExp
  exact lt_min (by positivity) (by positivity)

theorem sixWExp_le_one {Eb : Nat → Real → Real → Real → Real} {alpha t : Real}
    (hE : ∀ l g u s, 0 < s → s ≤ 1 → 0 < Eb l g u s ∧ Eb l g u s ≤ 1)
    (ht : 0 < t) (ht1 : t ≤ 1) : sixWExp Eb alpha t ≤ 1 := by
  have h2 := (hE 2 (alpha / 2) (globalBudget alpha (alpha / 2) 2) (t / 2 / 2)
    (by positivity) (by linarith)).2
  unfold sixWExp
  exact (min_le_right _ _).trans (by linarith)
end LeanProofs.GowersSzemeredi
