import ExponentialIdentities.TwoBaseIntegerExponent

namespace LeanProofs.TwoBaseIntegerExponent

open Set

/-- A table of the integers immediately below `m ^ (log 3 / log 2)` for `m < 100`.
The proof below does not trust this description: every entry is checked by exact natural-power
inequalities. -/
private def certifiedFloorBelowHundred : ℕ → ℕ
  | 1 => 1
  | 2 => 3
  | 3 => 5
  | 4 => 9
  | 5 => 12
  | 6 => 17
  | 7 => 21
  | 8 => 27
  | 9 => 32
  | 10 => 38
  | 11 => 44
  | 12 => 51
  | 13 => 58
  | 14 => 65
  | 15 => 73
  | 16 => 81
  | 17 => 89
  | 18 => 97
  | 19 => 106
  | 20 => 115
  | 21 => 124
  | 22 => 134
  | 23 => 143
  | 24 => 154
  | 25 => 164
  | 26 => 174
  | 27 => 185
  | 28 => 196
  | 29 => 207
  | 30 => 219
  | 31 => 231
  | 32 => 243
  | 33 => 255
  | 34 => 267
  | 35 => 280
  | 36 => 292
  | 37 => 305
  | 38 => 319
  | 39 => 332
  | 40 => 346
  | 41 => 359
  | 42 => 373
  | 43 => 388
  | 44 => 402
  | 45 => 417
  | 46 => 431
  | 47 => 446
  | 48 => 462
  | 49 => 477
  | 50 => 492
  | 51 => 508
  | 52 => 524
  | 53 => 540
  | 54 => 556
  | 55 => 573
  | 56 => 589
  | 57 => 606
  | 58 => 623
  | 59 => 640
  | 60 => 658
  | 61 => 675
  | 62 => 693
  | 63 => 711
  | 64 => 729
  | 65 => 747
  | 66 => 765
  | 67 => 783
  | 68 => 802
  | 69 => 821
  | 70 => 840
  | 71 => 859
  | 72 => 878
  | 73 => 898
  | 74 => 917
  | 75 => 937
  | 76 => 957
  | 77 => 977
  | 78 => 997
  | 79 => 1017
  | 80 => 1038
  | 81 => 1058
  | 82 => 1079
  | 83 => 1100
  | 84 => 1121
  | 85 => 1143
  | 86 => 1164
  | 87 => 1185
  | 88 => 1207
  | 89 => 1229
  | 90 => 1251
  | 91 => 1273
  | 92 => 1295
  | 93 => 1318
  | 94 => 1340
  | 95 => 1363
  | 96 => 1386
  | 97 => 1409
  | 98 => 1432
  | 99 => 1455
  | _ => 0

set_option maxHeartbeats 4000000 in
set_option exponentiation.threshold 600 in
/-- Exhaustive certificate covering every positive `m < 100`.  Powers of two are identified;
for every other value, the table entry `a` satisfies inequalities which put `m ^ α` in
`(a, a + 1)`. -/
private theorem certified_below_hundred (m : ℕ) (hmpos : 0 < m) (hmlt : m < 100) :
    (m = 1 ∨ m = 2 ∨ m = 4 ∨ m = 8 ∨ m = 16 ∨ m = 32 ∨ m = 64) ∨
      (0 < certifiedFloorBelowHundred m ∧
        certifiedFloorBelowHundred m ^ 359 < m ^ 569 ∧
        m ^ 485 < (certifiedFloorBelowHundred m + 1) ^ 306) := by
  interval_cases m <;> norm_num [certifiedFloorBelowHundred]

set_option exponentiation.threshold 600 in
private theorem two_pow_569_lt_three_pow_359 : 2 ^ 569 < 3 ^ 359 := by
  norm_num

set_option exponentiation.threshold 600 in
private theorem three_pow_306_lt_two_pow_485 : 3 ^ 306 < 2 ^ 485 := by
  norm_num

private theorem no_integer_strictly_between_consecutive_naturals'
    {y : ℝ} {a : ℕ}
    (hy : y ∈ Set.range ((↑) : ℤ → ℝ))
    (hlow : (a : ℝ) < y) (hupp : y < (a + 1 : ℕ)) : False := by
  obtain ⟨z, rfl⟩ := hy
  have hzlow : (a : ℤ) < z := by exact_mod_cast hlow
  have hzupp : z < (a : ℤ) + 1 := by exact_mod_cast hupp
  omega

private theorem mul_log_lt_mul_log_of_pow_lt'
    {a b p q : ℕ} (ha : 0 < a) (hb : 0 < b) (hpow : a ^ p < b ^ q) :
    (p : ℝ) * Real.log (a : ℝ) < (q : ℝ) * Real.log (b : ℝ) := by
  have hpowR : (a : ℝ) ^ p < (b : ℝ) ^ q := by exact_mod_cast hpow
  have hlog := Real.strictMonoOn_log
    (by simpa only [Set.mem_Ioi] using (show 0 < (a : ℝ) ^ p by positivity))
    (by simpa only [Set.mem_Ioi] using (show 0 < (b : ℝ) ^ q by positivity)) hpowR
  simpa only [Real.log_pow] using hlog

set_option exponentiation.threshold 600 in
/-- The rational bounds `569/359 < log 3 / log 2 < 485/306`, combined with the supplied
natural-power certificates, trap `3 ^ x` between consecutive integers. -/
private theorem not_three_rpow_integer_of_two_rpow_eq_tight
    {x : ℝ} {m a : ℕ}
    (h₂ : (2 : ℝ) ^ x = (m : ℝ))
    (h₃ : (3 : ℝ) ^ x ∈ Set.range ((↑) : ℤ → ℝ))
    (ha : 0 < a) (hxnonneg : 0 ≤ x)
    (hmLower : a ^ 359 < m ^ 569)
    (hmUpper : m ^ 485 < (a + 1) ^ 306) : False := by
  have hlogm := congrArg Real.log h₂
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)] at hlogm
  have hcommonLower :
      (569 : ℝ) * Real.log 2 < 359 * Real.log 3 :=
    mul_log_lt_mul_log_of_pow_lt' (by norm_num) (by norm_num) two_pow_569_lt_three_pow_359
  have hcommonUpper :
      (306 : ℝ) * Real.log 3 < 485 * Real.log 2 :=
    mul_log_lt_mul_log_of_pow_lt' (by norm_num) (by norm_num) three_pow_306_lt_two_pow_485
  have hmLowerLog :
      (359 : ℝ) * Real.log a < 569 * Real.log m :=
    mul_log_lt_mul_log_of_pow_lt' ha (by
      by_contra hm
      simp_all) hmLower
  have hmUpperLog :
      (485 : ℝ) * Real.log m < 306 * Real.log ((a + 1 : ℕ) : ℝ) :=
    mul_log_lt_mul_log_of_pow_lt' (by
      by_contra hm
      simp_all) (by omega) hmUpper
  have hLowerLog : Real.log a < x * Real.log 3 := by
    apply lt_of_mul_lt_mul_left _ (by norm_num : (0 : ℝ) ≤ 359)
    calc
      (359 : ℝ) * Real.log a < 569 * Real.log m := hmLowerLog
      _ = x * (569 * Real.log 2) := by rw [← hlogm]; ring
      _ ≤ x * (359 * Real.log 3) := mul_le_mul_of_nonneg_left hcommonLower.le hxnonneg
      _ = 359 * (x * Real.log 3) := by ring
  have hUpperLog : x * Real.log 3 < Real.log ((a + 1 : ℕ) : ℝ) := by
    apply lt_of_mul_lt_mul_left _ (by norm_num : (0 : ℝ) ≤ 306)
    calc
      (306 : ℝ) * (x * Real.log 3) = x * (306 * Real.log 3) := by ring
      _ ≤ x * (485 * Real.log 2) := mul_le_mul_of_nonneg_left hcommonUpper.le hxnonneg
      _ = 485 * Real.log m := by rw [← hlogm]; ring
      _ < 306 * Real.log ((a + 1 : ℕ) : ℝ) := hmUpperLog
  have hLower : (a : ℝ) < (3 : ℝ) ^ x := by
    rw [Real.lt_rpow_iff_log_lt (by positivity) (by norm_num : (0 : ℝ) < 3)]
    exact hLowerLog
  have hUpper : (3 : ℝ) ^ x < (a + 1 : ℕ) := by
    rw [Real.rpow_lt_iff_lt_log (by norm_num : (0 : ℝ) < 3) (by positivity)]
    exact hUpperLog
  exact no_integer_strictly_between_consecutive_naturals' h₃ hLower hUpper

/-- If both powers are integral and `2 ^ x < 100`, then `x` is an integer. -/
theorem integer_of_two_three_rpow_integer_of_two_rpow_lt_hundred {x : ℝ}
    (h₂ : (2 : ℝ) ^ x ∈ Set.range ((↑) : ℤ → ℝ))
    (h₃ : (3 : ℝ) ^ x ∈ Set.range ((↑) : ℤ → ℝ))
    (hlt : (2 : ℝ) ^ x < 100) :
    x ∈ Set.range ((↑) : ℤ → ℝ) := by
  obtain ⟨z, hz⟩ := h₂
  have hp : 0 < (2 : ℝ) ^ x := Real.rpow_pos_of_pos (by norm_num) _
  have hzpos : 0 < z := by exact_mod_cast (hz.symm ▸ hp)
  have hzlt : z < 100 := by exact_mod_cast (hz.symm ▸ hlt)
  have hxnonneg : 0 ≤ x := IntegerExponent.nonneg_of_two_rpow_integer ⟨z, hz⟩
  lift z to ℕ using hzpos.le with m hmcast
  have hmpos : 0 < m := by exact_mod_cast hzpos
  have hmlt : m < 100 := by exact_mod_cast hzlt
  have hpowm : (2 : ℝ) ^ x = (m : ℝ) := by
    exact hz.symm
  rcases certified_below_hundred m hmpos hmlt with hpowers | hcert
  · rcases hpowers with h1 | h2 | h4 | h8 | h16 | h32 | h64
    · refine ⟨0, ?_⟩
      have hx : x = 0 := by
        apply (Real.strictMono_rpow_of_base_gt_one (by norm_num : (1 : ℝ) < 2)).injective
        norm_num [h1] at hpowm ⊢
        exact hpowm
      exact_mod_cast hx.symm
    · refine ⟨1, ?_⟩
      have hx : x = 1 := by
        apply (Real.strictMono_rpow_of_base_gt_one (by norm_num : (1 : ℝ) < 2)).injective
        norm_num [h2] at hpowm ⊢
        exact hpowm
      exact_mod_cast hx.symm
    · refine ⟨2, ?_⟩
      have hx : x = 2 := by
        apply (Real.strictMono_rpow_of_base_gt_one (by norm_num : (1 : ℝ) < 2)).injective
        norm_num [h4] at hpowm ⊢
        simpa [Real.rpow_natCast] using hpowm
      exact_mod_cast hx.symm
    · refine ⟨3, ?_⟩
      have hx : x = 3 := by
        apply (Real.strictMono_rpow_of_base_gt_one (by norm_num : (1 : ℝ) < 2)).injective
        norm_num [h8] at hpowm ⊢
        simpa [Real.rpow_natCast] using hpowm
      exact_mod_cast hx.symm
    · refine ⟨4, ?_⟩
      have hx : x = 4 := by
        apply (Real.strictMono_rpow_of_base_gt_one (by norm_num : (1 : ℝ) < 2)).injective
        norm_num [h16] at hpowm ⊢
        simpa [Real.rpow_natCast] using hpowm
      exact_mod_cast hx.symm
    · refine ⟨5, ?_⟩
      have hx : x = 5 := by
        apply (Real.strictMono_rpow_of_base_gt_one (by norm_num : (1 : ℝ) < 2)).injective
        norm_num [h32] at hpowm ⊢
        simpa [Real.rpow_natCast] using hpowm
      exact_mod_cast hx.symm
    · refine ⟨6, ?_⟩
      have hx : x = 6 := by
        apply (Real.strictMono_rpow_of_base_gt_one (by norm_num : (1 : ℝ) < 2)).injective
        norm_num [h64] at hpowm ⊢
        simpa [Real.rpow_natCast] using hpowm
      exact_mod_cast hx.symm
  · exfalso
    exact not_three_rpow_integer_of_two_rpow_eq_tight hpowm h₃ hcert.1 hxnonneg
      hcert.2.1 hcert.2.2

/-- Every nonintegral two-base solution lies beyond the exact finite search region. -/
theorem hundred_le_two_rpow_of_not_integer_of_two_three_rpow_integer {x : ℝ}
    (h₂ : (2 : ℝ) ^ x ∈ Set.range ((↑) : ℤ → ℝ))
    (h₃ : (3 : ℝ) ^ x ∈ Set.range ((↑) : ℤ → ℝ))
    (hx : x ∉ Set.range ((↑) : ℤ → ℝ)) :
    100 ≤ (2 : ℝ) ^ x := by
  exact not_lt.mp fun hlt ↦ hx
    (integer_of_two_three_rpow_integer_of_two_rpow_lt_hundred h₂ h₃ hlt)

/-- In exponent coordinates, every nonintegral two-base solution is at least
`log 100 / log 2`. -/
theorem log_hundred_div_log_two_le_of_not_integer_of_two_three_rpow_integer {x : ℝ}
    (h₂ : (2 : ℝ) ^ x ∈ Set.range ((↑) : ℤ → ℝ))
    (h₃ : (3 : ℝ) ^ x ∈ Set.range ((↑) : ℤ → ℝ))
    (hx : x ∉ Set.range ((↑) : ℤ → ℝ)) :
    Real.log 100 / Real.log 2 ≤ x := by
  have hhundred :=
    hundred_le_two_rpow_of_not_integer_of_two_three_rpow_integer h₂ h₃ hx
  have hlog : Real.log 100 ≤ x * Real.log 2 :=
    (Real.le_rpow_iff_log_le (by norm_num : (0 : ℝ) < 100)
      (by norm_num : (0 : ℝ) < 2)).mp hhundred
  exact (div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).2 hlog

end LeanProofs.TwoBaseIntegerExponent
