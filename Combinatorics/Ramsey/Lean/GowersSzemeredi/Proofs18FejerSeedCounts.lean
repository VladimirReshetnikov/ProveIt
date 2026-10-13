import GowersSzemeredi.Proofs16PolyCoverTwoFejer
import GowersSzemeredi.Proofs18LengthSixExponents

/-! **The dimension-two counts under the Fejér θ₁** (Notes L.16d).

The Fejér analogue of `Proofs18LengthSixCounts`, in the base
`u = 2/(γθ)`, with the arrangement density
`θ₁′ = fejerThetaOne θ γ 1 = (θγ/4)^E`, `E = fejerProductExponent 1 = 229376`:

| quantity | printed degree | Fejér degree |
|---|---|---|
| `θ₁⁻¹` | `2^65` | `2^19` (`fejerThetaOne_one_inv_le`) |
| `θ′⁻¹` (budget) | `2^69` | `2^23` (`polyPieceBudgetW_fejer_inv_le_power`) |
| `δ⁻¹` | `2^68` | `2^22` (`section16Delta_fejer_one_inv_le`) |
| face and spectrum counts | `2^84` | `2^38` |
| pieces `⌊γ⁻²/(5θ′)⌋` | `2^70` | `2^24` |
| Lemma 15.6 threshold | `2^45` | `2^15` (`fejerProductThreshold_one_le_power`) |

The proofs are the corpus proofs with the new exponents, and they keep the
corpus's ordering: no `linarith` once a power `≥ 2^24` is in the context. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem fejerProductExponent_one : fejerProductExponent 1 = 229376 := by
  unfold fejerProductExponent fejerSelectionExponent; norm_num

/-- `θ₁′ ≥ u^(−2^19)`. -/
theorem fejerThetaOne_one_ge_power {gamma theta : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) :
    ((2 / (gamma * theta)) ^ ((2 : Nat) ^ 19))⁻¹ ≤ fejerThetaOne theta gamma 1 := by
  obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  have hq := quarter_prod_ge_inv_sq hg ht hu2
  set u := 2 / (gamma * theta) with hu
  clear_value u
  have hu1 : 1 ≤ u := by linarith
  have hupos : 0 < u := by linarith
  unfold fejerThetaOne
  have h := pow_le_pow_left₀ (by positivity) hq (fejerProductExponent 1)
  rw [inv_pow, ← pow_mul] at h
  refine le_trans ?_ h
  apply inv_anti₀ (pow_pos hupos _)
  apply pow_le_pow_right₀ hu1
  rw [fejerProductExponent_one]
  norm_num

theorem fejerThetaOne_one_inv_le {gamma theta : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) :
    (fejerThetaOne theta gamma 1)⁻¹ ≤ (2 / (gamma * theta)) ^ ((2 : Nat) ^ 19) := by
  obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  have hupos : 0 < 2 / (gamma * theta) := by linarith
  have h := fejerThetaOne_one_ge_power hg hg1 ht ht1
  have := inv_anti₀ (inv_pos.mpr (pow_pos hupos _)) h
  rwa [inv_inv] at this

theorem polyPieceBudgetW_fejer_ge_power {gamma theta : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) :
    ((2 / (gamma * theta)) ^ ((2 : Nat) ^ 23))⁻¹ ≤
      polyPieceBudgetW (fejerThetaOne theta gamma 1) := by
  obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  have hθ1 := fejerThetaOne_one_ge_power hg hg1 ht ht1
  set u := 2 / (gamma * theta) with hu
  clear_value u
  have hu1 : 1 ≤ u := by linarith
  have hupos : 0 < u := by linarith
  have h35 : (u ^ 35)⁻¹ ≤ (2 : Real) ^ (-(32 : Real)) / 8 := by
    have h1 : (2 : Real) ^ (-(32 : Real)) / 8 = ((2 : Real) ^ 35)⁻¹ := by
      rw [Real.rpow_neg (by norm_num)]
      norm_num
    rw [h1]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by norm_num) hu2 35)
  have hθ18 : (u ^ ((2 : Nat) ^ 22))⁻¹ ≤ fejerThetaOne theta gamma 1 ^ 8 := by
    have h := pow_le_pow_left₀ (inv_nonneg.mpr (pow_pos hupos _).le) hθ1 8
    rw [inv_pow, ← pow_mul] at h
    refine le_trans ?_ h
    apply inv_anti₀ (pow_pos hupos _)
    apply pow_le_pow_right₀ hu1
    norm_num
  have hθ0 : 0 ≤ fejerThetaOne theta gamma 1 := by unfold fejerThetaOne; positivity
  unfold polyPieceBudgetW section16ThetaTwo
  calc (u ^ ((2 : Nat) ^ 23))⁻¹ ≤ (u ^ 35 * u ^ ((2 : Nat) ^ 22))⁻¹ := by
        apply inv_anti₀ (mul_pos (pow_pos hupos _) (pow_pos hupos _))
        rw [← pow_add]
        apply pow_le_pow_right₀ hu1
        norm_num
    _ = (u ^ 35)⁻¹ * (u ^ ((2 : Nat) ^ 22))⁻¹ := mul_inv _ _
    _ ≤ (2 : Real) ^ (-(32 : Real)) / 8 * fejerThetaOne theta gamma 1 ^ 8 :=
        mul_le_mul h35 hθ18 (inv_nonneg.mpr (pow_pos hupos _).le) (by positivity)
    _ = (2 : Real) ^ (-(32 : Real)) * fejerThetaOne theta gamma 1 ^ 8 / 8 := by ring

theorem polyPieceBudgetW_fejer_pos_le {gamma theta : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) :
    0 < polyPieceBudgetW (fejerThetaOne theta gamma 1) ∧
      polyPieceBudgetW (fejerThetaOne theta gamma 1) ≤ 1 := by
  obtain ⟨ha0, haS⟩ := fejerThetaOne_one_bounds ht ht1 hg hg1
  obtain ⟨h1, h2⟩ := section16ThetaTwo_pos_le_with ha0 haS
  unfold polyPieceBudgetW
  exact ⟨by linarith, by linarith⟩

theorem polyPieceBudgetW_fejer_inv_le_power {gamma theta : Real} (hg : 0 < gamma)
    (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1) :
    (polyPieceBudgetW (fejerThetaOne theta gamma 1))⁻¹ ≤ (2 / (gamma * theta)) ^ ((2 : Nat) ^ 23) := by
  obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  have hupos : 0 < 2 / (gamma * theta) := by linarith
  have h := polyPieceBudgetW_fejer_ge_power hg hg1 ht ht1
  have := inv_anti₀ (inv_pos.mpr (pow_pos hupos _)) h
  rwa [inv_inv] at this

/-- `δ(θ₁′)⁻¹ ≤ u^(2^22)`. -/
theorem section16Delta_fejer_one_inv_le {gamma theta : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) :
    (section16Delta (fejerThetaOne theta gamma 1))⁻¹ ≤ (2 / (gamma * theta)) ^ ((2 : Nat) ^ 22) := by
  obtain ⟨hu, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  obtain ⟨ha0, haS⟩ := fejerThetaOne_one_bounds ht ht1 hg hg1
  obtain ⟨h0, h1, -, -⟩ := section16_theta_delta_bounds_with ha0 haS
  exact (section16Delta_inv_le_pw hu (by norm_num) h0 h1
    (fejerThetaOne_one_inv_le hg hg1 ht ht1))

/-- The spectrum count `≤ u^(2^38)`. -/
theorem polyPieceSpecCountW_fejer_le_power {gamma theta : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) :
    (polyPieceSpecCountW (fejerThetaOne theta gamma 1) : Real) ≤
      (2 / (gamma * theta)) ^ ((2 : Nat) ^ 38) := by
  obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  obtain ⟨ha0, haS⟩ := fejerThetaOne_one_bounds ht ht1 hg hg1
  obtain ⟨-, -, hd0, hd1⟩ := section16_theta_delta_bounds_with ha0 haS
  obtain ⟨hb, hb1⟩ := polyPieceBudgetW_fejer_pos_le hg hg1 ht ht1
  have hdi := section16Delta_fejer_one_inv_le hg hg1 ht ht1
  have hbi := polyPieceBudgetW_fejer_inv_le_power hg hg1 ht ht1
  have hBF := section16BaseFamilyBound_le_dyadic_power hd0 hd1 hb hb1
  unfold polyPieceSpecCountW
  set d := section16Delta (fejerThetaOne theta gamma 1)
  set b := polyPieceBudgetW (fejerThetaOne theta gamma 1)
  set u := 2 / (gamma * theta) with hu
  clear_value u d b
  have hupos : 0 < u := lt_of_lt_of_le (by norm_num) hu2
  have hu1 : 1 ≤ u := le_trans (by norm_num) hu2
  have hbase : 2 / (d * b) ≤ u ^ (1 + ((2 : Nat) ^ 22 + (2 : Nat) ^ 23)) := by
    rw [show 2 / (d * b) = 2 * (d⁻¹ * b⁻¹) by field_simp, pow_add, pow_one, pow_add]
    exact mul_le_mul hu2 (mul_le_mul hdi hbi (inv_pos.mpr hb).le (pow_nonneg hupos.le _))
      (mul_nonneg (inv_pos.mpr hd0).le (inv_pos.mpr hb).le) hupos.le
  refine hBF.trans ?_
  calc (2 / (d * b)) ^ ((2 : Nat) ^ 14)
      ≤ (u ^ (1 + ((2 : Nat) ^ 22 + (2 : Nat) ^ 23))) ^ ((2 : Nat) ^ 14) :=
        pow_le_pow_left₀ (div_pos (by norm_num) (mul_pos hd0 hb)).le hbase _
    _ = u ^ ((1 + ((2 : Nat) ^ 22 + (2 : Nat) ^ 23)) * (2 : Nat) ^ 14) := (pow_mul _ _ _).symm
    _ ≤ u ^ ((2 : Nat) ^ 38) := pow_le_pow_right₀ hu1 (by norm_num)

/-- The face and slice count `≤ u^(2^38)`. -/
theorem polyPieceFaceCountW_fejer_le_power {gamma theta : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) :
    (polyPieceFaceCountW (fejerThetaOne theta gamma 1) gamma : Real) ≤
      (2 / (gamma * theta)) ^ ((2 : Nat) ^ 38) := by
  obtain ⟨hu2, -, h2g, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  obtain ⟨hb, hb1⟩ := polyPieceBudgetW_fejer_pos_le hg hg1 ht ht1
  have hbinv := polyPieceBudgetW_fejer_inv_le_power hg hg1 ht ht1
  have hBF := section16BaseFamilyBound_le_dyadic_power hg hg1 hb hb1
  unfold polyPieceFaceCountW
  set b := polyPieceBudgetW (fejerThetaOne theta gamma 1)
  set u := 2 / (gamma * theta) with hu
  clear_value u b
  have hu1 : 1 ≤ u := le_trans (by norm_num) hu2
  have hupos : 0 < u := lt_of_lt_of_le (by norm_num) hu2
  have hbase : 2 / (gamma * b) ≤ u ^ ((2 : Nat) ^ 23 + 1) := by
    rw [show 2 / (gamma * b) = 2 / gamma * b⁻¹ by field_simp]
    rw [pow_succ, mul_comm (u ^ _) u]
    exact mul_le_mul h2g hbinv (inv_pos.mpr hb).le hupos.le
  refine hBF.trans ?_
  calc (2 / (gamma * b)) ^ ((2 : Nat) ^ 14)
      ≤ (u ^ ((2 : Nat) ^ 23 + 1)) ^ ((2 : Nat) ^ 14) :=
        pow_le_pow_left₀ (div_pos (by norm_num) (mul_pos hg hb)).le hbase _
    _ = u ^ (((2 : Nat) ^ 23 + 1) * (2 : Nat) ^ 14) := (pow_mul _ _ _).symm
    _ ≤ u ^ ((2 : Nat) ^ 38) := pow_le_pow_right₀ hu1 (by norm_num)

/-- The number of pieces `⌊γ⁻²/(5θ′)⌋ ≤ u^(2^24)`. -/
theorem polyTwoFejerPieces_le_power {gamma theta : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) :
    (polyTwoFejerPieces gamma theta : Real) ≤ (2 / (gamma * theta)) ^ ((2 : Nat) ^ 24) := by
  obtain ⟨hu2, hginv, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  obtain ⟨hb, hb1⟩ := polyPieceBudgetW_fejer_pos_le hg hg1 ht ht1
  have hb5 : (5 * polyPieceBudgetW (fejerThetaOne theta gamma 1))⁻¹ ≤
      (polyPieceBudgetW (fejerThetaOne theta gamma 1))⁻¹ :=
    inv_anti₀ hb (by linarith)
  have hbinv := polyPieceBudgetW_fejer_inv_le_power hg hg1 ht ht1
  set u := 2 / (gamma * theta) with hu
  clear_value u
  have hu1 : 1 ≤ u := le_trans (by norm_num) hu2
  have hupos : 0 < u := lt_of_lt_of_le (by norm_num) hu2
  have hg2 : gamma ^ (-(2 : Int)) ≤ u ^ 2 := by
    rw [zpow_neg, zpow_ofNat, ← inv_pow]
    exact pow_le_pow_left₀ (inv_pos.mpr hg).le hginv 2
  have hgz : 0 ≤ gamma ^ (-(2 : Int)) := zpow_nonneg hg.le _
  unfold polyTwoFejerPieces
  refine (Nat.floor_le (div_nonneg hgz (by positivity))).trans ?_
  calc gamma ^ (-(2 : Int)) / (5 * polyPieceBudgetW (fejerThetaOne theta gamma 1))
      ≤ gamma ^ (-(2 : Int)) * (polyPieceBudgetW (fejerThetaOne theta gamma 1))⁻¹ := by
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left hb5 hgz
    _ ≤ u ^ 2 * u ^ ((2 : Nat) ^ 23) :=
        mul_le_mul hg2 hbinv (inv_pos.mpr hb).le (pow_pos hupos _).le
    _ = u ^ (2 + (2 : Nat) ^ 23) := (pow_add _ _ _).symm
    _ ≤ u ^ ((2 : Nat) ^ 24) := pow_le_pow_right₀ hu1 (by norm_num)

/-! ### The Fejér Lemma 15.6 threshold at `k = 1` -/

/-- **The Fejér Lemma 15.6 threshold is at most `u^(2^15)`**, against
`u^(2^45)` for the printed one. -/
theorem fejerProductThreshold_one_le_power {gamma theta : Real} (hg : 0 < gamma)
    (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1) :
    fejerProductThreshold 1 (theta / 2) gamma ≤ (2 / (gamma * theta)) ^ ((2 : Nat) ^ 15) := by
  obtain ⟨hu2, -, -, h1, h2⟩ := prod_scale_basic hg hg1 ht ht1
  set u := 2 / (gamma * theta) with hu
  clear_value u
  have hu1 : 1 ≤ u := le_trans (by norm_num) hu2
  have hupos : 0 < u := lt_of_lt_of_le (by norm_num) hu2
  -- the selection base `α = (θ/2)^112 γ^336 ≥ u^(-448)`
  have hbase : (u ^ 448)⁻¹ ≤ (theta / 2) ^ (7 * 4 ^ (1 + 1)) * gamma ^ (21 * 1 * 4 ^ (1 + 1)) := by
    have hp1 := pow_le_pow_left₀ (inv_pos.mpr hupos).le h1 (7 * 4 ^ (1 + 1))
    have hp2 := pow_le_pow_left₀ (inv_pos.mpr hupos).le h2 (21 * 1 * 4 ^ (1 + 1))
    calc (u ^ 448)⁻¹ = u⁻¹ ^ (7 * 4 ^ (1 + 1)) * u⁻¹ ^ (21 * 1 * 4 ^ (1 + 1)) := by
          rw [← pow_add, inv_pow]; norm_num
      _ ≤ _ := mul_le_mul hp1 hp2 (by positivity) (by positivity)
  set a := (theta / 2) ^ (7 * 4 ^ (1 + 1)) * gamma ^ (21 * 1 * 4 ^ (1 + 1)) with ha
  have hapos : 0 < a := lt_of_lt_of_le (by positivity) hbase
  have ha1 : a ≤ 1 := by
    rw [ha]
    exact mul_le_one₀ (pow_le_one₀ (by positivity) (by linarith)) (by positivity)
      (pow_le_one₀ hg.le hg1)
  have hmin : min a 1 = a := min_eq_left ha1
  set eta : Real := (2 : Real)⁻¹ ^ 44 with heta
  have heta0 : 0 < eta := by rw [heta]; positivity
  have h44 : (u ^ 44)⁻¹ ≤ eta := by
    rw [heta, inv_pow]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by norm_num) hu2 44)
  -- `6/(aη) ≤ u^495`
  have hae : (u ^ 492)⁻¹ ≤ a * eta := by
    calc (u ^ 492)⁻¹ = (u ^ 448)⁻¹ * (u ^ 44)⁻¹ := by rw [← mul_inv, ← pow_add]
      _ ≤ a * eta := mul_le_mul hbase h44 (by positivity) hapos.le
  have hsix : 6 / (min a 1 * eta) ≤ u ^ 495 := by
    rw [hmin, div_le_iff₀ (mul_pos hapos heta0)]
    have h6 : (6 : Real) ≤ u ^ 3 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0:Real) ≤ 2) hu2 3]
    have hinv : 1 ≤ u ^ 492 * (a * eta) := by
      have := mul_le_mul_of_nonneg_left hae (pow_pos hupos 492).le
      rwa [mul_inv_cancel₀ (pow_pos hupos 492).ne'] at this
    calc (6 : Real) ≤ u ^ 3 * 1 := by rw [mul_one]; exact h6
      _ ≤ u ^ 3 * (u ^ 492 * (a * eta)) := mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = u ^ 495 * (a * eta) := by rw [← mul_assoc, ← pow_add]
  have hT : ((⌈6 / (min a 1 * eta)⌉₊ : Nat) : Real) ≤ u ^ 496 :=
    ceil_le_pow_succ hu2 (by rw [hmin]; positivity) hsix
  have hT1 : 1 ≤ ⌈6 / (min a 1 * eta)⌉₊ := by
    rw [Nat.one_le_ceil_iff, hmin]; positivity
  -- `m + 1 ≤ u^501`
  have hm1 : ((fejerOrder 1 a eta : Nat) : Real) + 1 ≤ u ^ 501 := by
    unfold fejerOrder
    have hpos : 1 ≤ 2 ^ (1 + 4) * ⌈6 / (min a 1 * eta)⌉₊ := by
      have : 1 ≤ 2 ^ (1 + 4) := Nat.one_le_two_pow
      exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    have hcast : ((2 ^ (1 + 4) * ⌈6 / (min a 1 * eta)⌉₊ - 1 : Nat) : Real) + 1 =
        32 * ((⌈6 / (min a 1 * eta)⌉₊ : Nat) : Real) := by
      rw [Nat.cast_sub hpos]; push_cast; ring
    rw [hcast]
    calc 32 * ((⌈6 / (min a 1 * eta)⌉₊ : Nat) : Real) ≤ u ^ 5 * u ^ 496 :=
          mul_le_mul (by nlinarith [pow_le_pow_left₀ (by norm_num : (0:Real) ≤ 2) hu2 5])
            hT (Nat.cast_nonneg _) (by positivity)
      _ = u ^ 501 := by rw [← pow_add]
  set m : Nat := fejerOrder 1 a eta with hmdef
  have hmpos : (0 : Real) < (m : Real) + 1 := by positivity
  have h2m : 2 * (m : Real) + 1 ≤ u ^ 502 := by
    have : 2 * (m : Real) + 1 ≤ 2 * ((m : Real) + 1) := by linarith
    calc 2 * (m : Real) + 1 ≤ 2 * ((m : Real) + 1) := this
      _ ≤ u * u ^ 501 := mul_le_mul hu2 hm1 hmpos.le hupos.le
      _ = u ^ 502 := by rw [← pow_succ']
  -- the degenerate quotient `2 c₀ / t ≤ u^(2^15)`
  have hc0 : fejerDegenerateConst 1 a eta ≤ u ^ (502 * 32) := by
    unfold fejerDegenerateConst
    rw [← hmdef, show (2 * 8 * 2 ^ 1 : Nat) = 32 from rfl, Nat.cast_one, mul_one, pow_mul]
    exact pow_le_pow_left₀ (by positivity) h2m 32
  have htinv : (fejerLoss 1 a eta)⁻¹ ≤ u ^ (501 * 32) := by
    unfold fejerLoss
    rw [← hmdef, pow_mul, inv_pow, inv_inv]
    have : ((m : Real) + 1) ^ (2 ^ (1 + 4)) = ((m : Real) + 1) ^ 32 := by norm_num
    rw [this]
    exact pow_le_pow_left₀ hmpos.le hm1 32
  have htpos : 0 < fejerLoss 1 a eta := by unfold fejerLoss; positivity
  unfold fejerProductThreshold fejerExplicitThreshold
  rw [← ha, ← heta, ← hmdef]
  apply max_le
  · exact hm1.trans (pow_le_pow_right₀ hu1 (by norm_num))
  · apply max_le
    · nlinarith [pow_le_pow_right₀ hu1 (show 2 ≤ (2 : Nat) ^ 15 by norm_num),
        pow_le_pow_left₀ (by norm_num : (0:Real) ≤ 2) hu2 2]
    · rw [one_mul, div_eq_mul_inv]
      calc 2 * fejerDegenerateConst 1 a eta * (fejerLoss 1 a eta)⁻¹
          ≤ u * u ^ (502 * 32) * u ^ (501 * 32) :=
            mul_le_mul (mul_le_mul hu2 hc0 (by unfold fejerDegenerateConst; positivity)
              hupos.le) htinv (inv_pos.mpr htpos).le (by positivity)
        _ = u ^ (1 + 502 * 32 + 501 * 32) := by rw [← pow_succ', ← pow_add]
        _ ≤ u ^ ((2 : Nat) ^ 15) := pow_le_pow_right₀ hu1 (by norm_num)

/-- The Fejér dimension-two threshold is at most `u^(2^15)`. -/
theorem polyTwoFejerThreshold_le_power {gamma theta : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) :
    polyTwoFejerThreshold theta gamma ≤ (2 / (gamma * theta)) ^ ((2 : Nat) ^ 15) := by
  obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  have hu3 : (3 : Real) ≤ (2 / (gamma * theta)) ^ 2 := by nlinarith
  unfold polyTwoFejerThreshold
  apply max_le
  · exact hu3.trans (pow_le_pow_right₀ (by linarith) (by norm_num))
  · exact fejerProductThreshold_one_le_power hg hg1 ht ht1

end LeanProofs.GowersSzemeredi
