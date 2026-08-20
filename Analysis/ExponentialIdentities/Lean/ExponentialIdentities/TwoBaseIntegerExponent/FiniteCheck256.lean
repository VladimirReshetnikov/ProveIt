import ExponentialIdentities.TwoBaseIntegerExponent.FiniteCheck

namespace LeanProofs.TwoBaseIntegerExponent

open Set

/-!
This file extends the exact finite verification from `100` to `256`.  It uses three
rational enclosures of `log 3 / log 2`; the expensive third enclosure is needed for
only five values.  Every numerical claim is proved by `norm_num`, hence replayed by
the Lean kernel.
-/

private def certifiedFloorFrom100To255 : ℕ → ℕ
  | 100 => 1478
  | 101 => 1502
  | 102 => 1526
  | 103 => 1549
  | 104 => 1573
  | 105 => 1597
  | 106 => 1621
  | 107 => 1646
  | 108 => 1670
  | 109 => 1695
  | 110 => 1720
  | 111 => 1744
  | 112 => 1769
  | 113 => 1794
  | 114 => 1820
  | 115 => 1845
  | 116 => 1871
  | 117 => 1896
  | 118 => 1922
  | 119 => 1948
  | 120 => 1974
  | 121 => 2000
  | 122 => 2026
  | 123 => 2053
  | 124 => 2079
  | 125 => 2106
  | 126 => 2133
  | 127 => 2159
  | 128 => 2186
  | 129 => 2214
  | 130 => 2241
  | 131 => 2268
  | 132 => 2296
  | 133 => 2323
  | 134 => 2351
  | 135 => 2379
  | 136 => 2407
  | 137 => 2435
  | 138 => 2463
  | 139 => 2492
  | 140 => 2520
  | 141 => 2549
  | 142 => 2578
  | 143 => 2606
  | 144 => 2635
  | 145 => 2664
  | 146 => 2694
  | 147 => 2723
  | 148 => 2752
  | 149 => 2782
  | 150 => 2812
  | 151 => 2841
  | 152 => 2871
  | 153 => 2901
  | 154 => 2931
  | 155 => 2962
  | 156 => 2992
  | 157 => 3022
  | 158 => 3053
  | 159 => 3084
  | 160 => 3114
  | 161 => 3145
  | 162 => 3176
  | 163 => 3208
  | 164 => 3239
  | 165 => 3270
  | 166 => 3302
  | 167 => 3333
  | 168 => 3365
  | 169 => 3397
  | 170 => 3429
  | 171 => 3461
  | 172 => 3493
  | 173 => 3525
  | 174 => 3557
  | 175 => 3590
  | 176 => 3622
  | 177 => 3655
  | 178 => 3688
  | 179 => 3721
  | 180 => 3754
  | 181 => 3787
  | 182 => 3820
  | 183 => 3853
  | 184 => 3887
  | 185 => 3920
  | 186 => 3954
  | 187 => 3988
  | 188 => 4022
  | 189 => 4056
  | 190 => 4090
  | 191 => 4124
  | 192 => 4158
  | 193 => 4192
  | 194 => 4227
  | 195 => 4262
  | 196 => 4296
  | 197 => 4331
  | 198 => 4366
  | 199 => 4401
  | 200 => 4436
  | 201 => 4471
  | 202 => 4507
  | 203 => 4542
  | 204 => 4578
  | 205 => 4613
  | 206 => 4649
  | 207 => 4685
  | 208 => 4721
  | 209 => 4757
  | 210 => 4793
  | 211 => 4829
  | 212 => 4865
  | 213 => 4902
  | 214 => 4938
  | 215 => 4975
  | 216 => 5012
  | 217 => 5048
  | 218 => 5085
  | 219 => 5122
  | 220 => 5160
  | 221 => 5197
  | 222 => 5234
  | 223 => 5271
  | 224 => 5309
  | 225 => 5347
  | 226 => 5384
  | 227 => 5422
  | 228 => 5460
  | 229 => 5498
  | 230 => 5536
  | 231 => 5574
  | 232 => 5613
  | 233 => 5651
  | 234 => 5690
  | 235 => 5728
  | 236 => 5767
  | 237 => 5806
  | 238 => 5845
  | 239 => 5883
  | 240 => 5923
  | 241 => 5962
  | 242 => 6001
  | 243 => 6040
  | 244 => 6080
  | 245 => 6119
  | 246 => 6159
  | 247 => 6199
  | 248 => 6239
  | 249 => 6278
  | 250 => 6318
  | 251 => 6359
  | 252 => 6399
  | 253 => 6439
  | 254 => 6479
  | 255 => 6520
  | _ => 0

/-- Tier zero uses exponents around `500`, tier one around `1500`, and tier two around
`25000`. -/
private def certificateTierFrom100To255 (m : ℕ) : ℕ :=
  if m ∈ [163, 193, 223, 239, 250] then 2
  else if m ∈
      [102, 110, 127, 145, 150, 155, 160, 189, 195, 202, 204, 208, 217,
        218, 219, 220, 231, 234, 237, 238, 240, 248, 249, 251, 254] then 1
  else 0

private def TightCertificate (m a : ℕ) : Prop :=
  match certificateTierFrom100To255 m with
  | 0 => a ^ 359 < m ^ 569 ∧ m ^ 485 < (a + 1) ^ 306
  | 1 => a ^ 665 < m ^ 1054 ∧ m ^ 1539 < (a + 1) ^ 971
  | _ => a ^ 16266 < m ^ 25781 ∧ m ^ 24727 < (a + 1) ^ 15601

set_option maxHeartbeats 12000000 in
set_option exponentiation.threshold 26000 in
private theorem certified_from_100_to_255 (m : ℕ) (hmlo : 100 ≤ m) (hmhi : m < 256) :
    m = 128 ∨
      (0 < certifiedFloorFrom100To255 m ∧
        TightCertificate m (certifiedFloorFrom100To255 m)) := by
  interval_cases m <;>
    norm_num [certifiedFloorFrom100To255, TightCertificate, certificateTierFrom100To255]

private theorem mul_log_lt_mul_log_of_pow_lt256
    {a b p q : ℕ} (ha : 0 < a) (hb : 0 < b) (hpow : a ^ p < b ^ q) :
    (p : ℝ) * Real.log (a : ℝ) < (q : ℝ) * Real.log (b : ℝ) := by
  have hpowR : (a : ℝ) ^ p < (b : ℝ) ^ q := by exact_mod_cast hpow
  have hlog := Real.strictMonoOn_log
    (by simpa only [Set.mem_Ioi] using (show 0 < (a : ℝ) ^ p by positivity))
    (by simpa only [Set.mem_Ioi] using (show 0 < (b : ℝ) ^ q by positivity)) hpowR
  simpa only [Real.log_pow] using hlog

private theorem no_integer_between_consecutive_naturals256
    {y : ℝ} {a : ℕ}
    (hy : y ∈ Set.range ((↑) : ℤ → ℝ))
    (hlow : (a : ℝ) < y) (hupp : y < (a + 1 : ℕ)) : False := by
  obtain ⟨z, rfl⟩ := hy
  have hzlow : (a : ℤ) < z := by exact_mod_cast hlow
  have hzupp : z < (a : ℤ) + 1 := by exact_mod_cast hupp
  omega

/-- A generic rational enclosure of `log 3 / log 2`, together with a matching
local enclosure of `m`'s power, traps `3 ^ x` between consecutive integers. -/
private theorem not_three_rpow_integer_of_two_rpow_eq_certificate256
    {x : ℝ} {m a lowerNum lowerDen upperNum upperDen : ℕ}
    (h₂ : (2 : ℝ) ^ x = (m : ℝ))
    (h₃ : (3 : ℝ) ^ x ∈ Set.range ((↑) : ℤ → ℝ))
    (ha : 0 < a) (hmpos : 0 < m) (hxnonneg : 0 ≤ x)
    (hlowerDenPos : 0 < lowerDen) (hupperDenPos : 0 < upperDen)
    (hlowerBase : 2 ^ lowerNum < 3 ^ lowerDen)
    (hupperBase : 3 ^ upperDen < 2 ^ upperNum)
    (hmLower : a ^ lowerDen < m ^ lowerNum)
    (hmUpper : m ^ upperNum < (a + 1) ^ upperDen) : False := by
  have hlogm := congrArg Real.log h₂
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)] at hlogm
  have hcommonLower :
      (lowerNum : ℝ) * Real.log 2 < lowerDen * Real.log 3 :=
    mul_log_lt_mul_log_of_pow_lt256 (by norm_num) (by norm_num) hlowerBase
  have hcommonUpper :
      (upperDen : ℝ) * Real.log 3 < upperNum * Real.log 2 :=
    mul_log_lt_mul_log_of_pow_lt256 (by norm_num) (by norm_num) hupperBase
  have hmLowerLog :
      (lowerDen : ℝ) * Real.log a < lowerNum * Real.log m :=
    mul_log_lt_mul_log_of_pow_lt256 ha hmpos hmLower
  have hmUpperLog :
      (upperNum : ℝ) * Real.log m < upperDen * Real.log ((a + 1 : ℕ) : ℝ) :=
    mul_log_lt_mul_log_of_pow_lt256 hmpos (by omega) hmUpper
  have hlowerDenPosR : (0 : ℝ) < lowerDen := by exact_mod_cast hlowerDenPos
  have hupperDenPosR : (0 : ℝ) < upperDen := by exact_mod_cast hupperDenPos
  have hLowerLog : Real.log a < x * Real.log 3 := by
    apply lt_of_mul_lt_mul_left _ hlowerDenPosR.le
    calc
      (lowerDen : ℝ) * Real.log a < lowerNum * Real.log m := hmLowerLog
      _ = x * (lowerNum * Real.log 2) := by rw [← hlogm]; ring
      _ ≤ x * (lowerDen * Real.log 3) := mul_le_mul_of_nonneg_left hcommonLower.le hxnonneg
      _ = lowerDen * (x * Real.log 3) := by ring
  have hUpperLog : x * Real.log 3 < Real.log ((a + 1 : ℕ) : ℝ) := by
    apply lt_of_mul_lt_mul_left _ hupperDenPosR.le
    calc
      (upperDen : ℝ) * (x * Real.log 3) = x * (upperDen * Real.log 3) := by ring
      _ ≤ x * (upperNum * Real.log 2) := mul_le_mul_of_nonneg_left hcommonUpper.le hxnonneg
      _ = upperNum * Real.log m := by rw [← hlogm]; ring
      _ < upperDen * Real.log ((a + 1 : ℕ) : ℝ) := hmUpperLog
  have hLower : (a : ℝ) < (3 : ℝ) ^ x := by
    rw [Real.lt_rpow_iff_log_lt (by positivity) (by norm_num : (0 : ℝ) < 3)]
    exact hLowerLog
  have hUpper : (3 : ℝ) ^ x < (a + 1 : ℕ) := by
    rw [Real.rpow_lt_iff_lt_log (by norm_num : (0 : ℝ) < 3) (by positivity)]
    exact hUpperLog
  exact no_integer_between_consecutive_naturals256 h₃ hLower hUpper

set_option exponentiation.threshold 26000 in
private theorem lower_bound_tier0 : 2 ^ 569 < 3 ^ 359 := by norm_num
set_option exponentiation.threshold 26000 in
private theorem upper_bound_tier0 : 3 ^ 306 < 2 ^ 485 := by norm_num
set_option exponentiation.threshold 26000 in
private theorem lower_bound_tier1 : 2 ^ 1054 < 3 ^ 665 := by norm_num
set_option exponentiation.threshold 26000 in
private theorem upper_bound_tier1 : 3 ^ 971 < 2 ^ 1539 := by norm_num
set_option exponentiation.threshold 26000 in
private theorem lower_bound_tier2 : 2 ^ 25781 < 3 ^ 16266 := by norm_num
set_option exponentiation.threshold 26000 in
private theorem upper_bound_tier2 : 3 ^ 15601 < 2 ^ 24727 := by norm_num

private theorem contradiction_from_tight_certificate256
    {x : ℝ} {m a : ℕ}
    (h₂ : (2 : ℝ) ^ x = (m : ℝ))
    (h₃ : (3 : ℝ) ^ x ∈ Set.range ((↑) : ℤ → ℝ))
    (ha : 0 < a) (hmpos : 0 < m) (hxnonneg : 0 ≤ x)
    (hcert : TightCertificate m a) : False := by
  rw [TightCertificate] at hcert
  split at hcert
  · exact not_three_rpow_integer_of_two_rpow_eq_certificate256 h₂ h₃ ha hmpos hxnonneg
      (by norm_num) (by norm_num) lower_bound_tier0 upper_bound_tier0 hcert.1 hcert.2
  · exact not_three_rpow_integer_of_two_rpow_eq_certificate256 h₂ h₃ ha hmpos hxnonneg
      (by norm_num) (by norm_num) lower_bound_tier1 upper_bound_tier1 hcert.1 hcert.2
  · exact not_three_rpow_integer_of_two_rpow_eq_certificate256 h₂ h₃ ha hmpos hxnonneg
      (by norm_num) (by norm_num) lower_bound_tier2 upper_bound_tier2 hcert.1 hcert.2

/-- If both powers are integral and `2 ^ x < 256`, then `x` is an integer. -/
theorem integer_of_two_three_rpow_integer_of_two_rpow_lt_256 {x : ℝ}
    (h₂ : (2 : ℝ) ^ x ∈ Set.range ((↑) : ℤ → ℝ))
    (h₃ : (3 : ℝ) ^ x ∈ Set.range ((↑) : ℤ → ℝ))
    (hlt : (2 : ℝ) ^ x < 256) :
    x ∈ Set.range ((↑) : ℤ → ℝ) := by
  by_cases hsmall : (2 : ℝ) ^ x < 100
  · exact integer_of_two_three_rpow_integer_of_two_rpow_lt_hundred h₂ h₃ hsmall
  obtain ⟨z, hz⟩ := h₂
  have hp : 0 < (2 : ℝ) ^ x := Real.rpow_pos_of_pos (by norm_num) _
  have hzpos : 0 < z := by exact_mod_cast (hz.symm ▸ hp)
  have hzloR : (100 : ℝ) ≤ (z : ℝ) := by
    calc
      (100 : ℝ) ≤ 2 ^ x := not_lt.mp hsmall
      _ = (z : ℝ) := hz.symm
  have hzlo : 100 ≤ z := by exact_mod_cast hzloR
  have hzhi : z < 256 := by exact_mod_cast (hz.symm ▸ hlt)
  have hxnonneg : 0 ≤ x := IntegerExponent.nonneg_of_two_rpow_integer ⟨z, hz⟩
  lift z to ℕ using hzpos.le with m hmcast
  have hmlo : 100 ≤ m := by exact_mod_cast hzlo
  have hmhi : m < 256 := by exact_mod_cast hzhi
  have hpowm : (2 : ℝ) ^ x = (m : ℝ) := hz.symm
  rcases certified_from_100_to_255 m hmlo hmhi with h128 | hcert
  · refine ⟨7, ?_⟩
    have hx : x = 7 := by
      apply (Real.strictMono_rpow_of_base_gt_one (by norm_num : (1 : ℝ) < 2)).injective
      norm_num [h128] at hpowm ⊢
      simpa [Real.rpow_natCast] using hpowm
    exact_mod_cast hx.symm
  · exfalso
    exact contradiction_from_tight_certificate256 hpowm h₃ hcert.1
      (by omega) hxnonneg hcert.2

/-- In exponent coordinates, every nonintegral two-base solution is at least `8`. -/
theorem eight_le_of_not_integer_of_two_three_rpow_integer {x : ℝ}
    (h₂ : (2 : ℝ) ^ x ∈ Set.range ((↑) : ℤ → ℝ))
    (h₃ : (3 : ℝ) ^ x ∈ Set.range ((↑) : ℤ → ℝ))
    (hx : x ∉ Set.range ((↑) : ℤ → ℝ)) :
    (8 : ℝ) ≤ x := by
  have h256 : (256 : ℝ) ≤ (2 : ℝ) ^ x :=
    not_lt.mp fun hlt ↦ hx
      (integer_of_two_three_rpow_integer_of_two_rpow_lt_256 h₂ h₃ hlt)
  apply (Real.strictMono_rpow_of_base_gt_one (by norm_num : (1 : ℝ) < 2)).le_iff_le.mp
  norm_num [Real.rpow_natCast]
  exact h256

end LeanProofs.TwoBaseIntegerExponent
