import GowersSzemeredi.Proofs18LengthSixScale

/-! Polynomial bounds on the graph counts of the length-six route.

The density `β` of the final discrepancy bound depends only on the graph
counts `sixQb` (through the lift densities `sixC`), not on the width
exponents. Here every count is bounded by a power of
`u = 2/(γ θ ρ)`:
* `section16BaseFamilyBound γ θ ≤ u^(2^14)`;
* Lemma 15.6's threshold, the piece count `polyTwoPieces` and the face
  count `polyPieceFaceCount` by explicit powers;
* `sixQb l γ θ ρ ≤ (2/(γθρ))^(2^90)` (`sixQb_le_power`).

Degrees are kept as powers of two, so the final comparison only adds
exponents. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open BaseCase

/-! ### Power calculus -/

theorem pow_le_pow_of_base_le {x y : Real} (hy : 0 ≤ y) (hxy : y ≤ x) (n : Nat) :
    y ^ n ≤ x ^ n := pow_le_pow_left₀ hy hxy n

theorem pow_mono_exp {x : Real} (hx : 1 ≤ x) {a b : Nat} (hab : a ≤ b) : x ^ a ≤ x ^ b :=
  pow_le_pow_right₀ hx hab

/-- `y ≤ x^a`, `z ≤ x^b` give `y z ≤ x^(a+b)`. -/
theorem mul_le_pow_add {x y z : Real} {a b : Nat} (hy0 : 0 ≤ y) (hz0 : 0 ≤ z)
    (hy : y ≤ x ^ a) (hz : z ≤ x ^ b) (hx : 0 ≤ x) : y * z ≤ x ^ (a + b) := by
  rw [pow_add]
  exact mul_le_mul hy hz hz0 (pow_nonneg hx _)

/-- A sum of two powers is below the next power, for `x ≥ 2`. -/
theorem add_le_pow_succ {x y z : Real} {a : Nat} (hx : 2 ≤ x) (hy : y ≤ x ^ a) (hz : z ≤ x ^ a) :
    y + z ≤ x ^ (a + 1) := by
  rw [pow_succ]
  have h := pow_nonneg (show (0 : Real) ≤ x by linarith) a
  nlinarith

/-- `⌈y⌉ ≤ x^(a+1)` when `0 ≤ y ≤ x^a` and `x ≥ 2`. -/
theorem ceil_le_pow_succ {x y : Real} {a : Nat} (hx : 2 ≤ x) (hy0 : 0 ≤ y) (hy : y ≤ x ^ a) :
    (⌈y⌉₊ : Real) ≤ x ^ (a + 1) := by
  have h1 : (⌈y⌉₊ : Real) ≤ y + 1 := (Nat.ceil_lt_add_one hy0).le
  have h2 : (1 : Real) ≤ x ^ a := one_le_pow₀ (by linarith)
  exact h1.trans (add_le_pow_succ hx hy h2)

/-! ### The base family bound -/

/-- `section16BaseFamilyBound γ θ ≤ (2/(γθ))^(2^14)`. -/
theorem section16BaseFamilyBound_le_power {gamma theta : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) :
    (section16BaseFamilyBound gamma theta : Real) ≤ (2 / (gamma * theta)) ^ ((2 : Nat) ^ 14) := by
  set u := 2 / (gamma * theta) with hu
  have hgt : 0 < gamma * theta := mul_pos hg ht
  have hgt1 : gamma * theta ≤ 1 := mul_le_one₀ hg1 ht.le ht1
  have hu2 : 2 ≤ u := by rw [hu, le_div_iff₀ hgt]; linarith
  have hu1 : 1 ≤ u := by linarith
  have hu0 : 0 ≤ u := by linarith
  -- 1/γ ≤ u and 1/(γθ) ≤ u
  have hinv : (gamma * theta)⁻¹ ≤ u := by
    rw [hu, div_eq_mul_inv]; linarith [inv_pos.mpr hgt]
  have hginv : gamma⁻¹ ≤ u := by
    refine le_trans ?_ hinv
    exact inv_anti₀ hgt (by nlinarith)
  -- the ratio γ⁻² / α163
  have hα := lemma163Alpha_pos hg ht
  have hratio : gamma ^ (-(2 : Int)) / lemma163Alpha gamma theta ≤ u ^ 12002 := by
    unfold lemma163Alpha
    have h2000 : (2 : Real) ^ (2000 : Real) ≤ u ^ 2000 := by
      rw [show (2000 : Real) = ((2000 : Nat) : Real) by norm_num, Real.rpow_natCast]
      exact pow_le_pow_left₀ (by norm_num) hu2 _
    have hg2 : gamma ^ (-(2 : Int)) ≤ u ^ 2 := by
      rw [zpow_neg, zpow_ofNat, ← inv_pow]
      exact pow_le_pow_left₀ (by positivity) hginv 2
    have hgt10 : ((gamma * theta) ^ (10000 : Nat))⁻¹ ≤ u ^ 10000 := by
      rw [← inv_pow]
      exact pow_le_pow_left₀ (by positivity) hinv _
    rw [div_eq_mul_inv, mul_inv, Real.rpow_neg (by norm_num), inv_inv]
    calc gamma ^ (-(2 : Int)) * ((2 : Real) ^ (2000 : Real) * ((gamma * theta) ^ (10000 : Nat))⁻¹)
        ≤ u ^ 2 * (u ^ 2000 * u ^ 10000) := by
          apply mul_le_mul hg2 (mul_le_mul h2000 hgt10 (by positivity) (by positivity))
            (by positivity) (by positivity)
      _ = u ^ 12002 := by rw [← pow_add, ← pow_add]
  unfold section16BaseFamilyBound
  rw [Nat.cast_max, Nat.cast_one]
  apply max_le
  · exact one_le_pow₀ hu1
  · refine (Nat.floor_le (by positivity)).trans (hratio.trans ?_)
    exact pow_le_pow_right₀ hu1 (by norm_num)


/-! ### The piece budget, the face count and the piece count

Trap: `linarith` (through `cancel_denoms`) evaluates `1 ^ n` as a runtime
`Nat.pow` for every power atom `x ^ n` in the context, which panics once
`n ≥ 2^24`. Every arithmetic fact below is therefore derived before the
first hypothesis with a huge exponent enters the context. -/

/-- The elementary facts about `u = 2/(γθ)` for `γ, θ ∈ (0, 1]`. -/
theorem prod_scale_basic {gamma theta : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) :
    2 ≤ 2 / (gamma * theta) ∧ gamma⁻¹ ≤ 2 / (gamma * theta) ∧
      2 / gamma ≤ 2 / (gamma * theta) ∧ (2 / (gamma * theta))⁻¹ ≤ theta / 2 ∧
      (2 / (gamma * theta))⁻¹ ≤ gamma := by
  have hgt : 0 < gamma * theta := mul_pos hg ht
  have hgt1 : gamma * theta ≤ 1 := mul_le_one₀ hg1 ht.le ht1
  have hgg : gamma * theta ≤ gamma := by nlinarith
  have hinv : (2 / (gamma * theta))⁻¹ = gamma * theta / 2 := by rw [inv_div]
  refine ⟨by rw [le_div_iff₀ hgt]; linarith, ?_, ?_, ?_, ?_⟩
  · rw [div_eq_mul_inv]
    have : gamma⁻¹ ≤ (gamma * theta)⁻¹ := inv_anti₀ hgt hgg
    linarith [inv_pos.mpr hgt]
  · exact div_le_div_of_nonneg_left (by norm_num) hgt hgg
  · rw [hinv]; nlinarith
  · rw [hinv]; nlinarith

/-- `(γθ/4) ≥ u⁻²` for `u = 2/(γθ) ≥ 2`. -/
theorem quarter_prod_ge_inv_sq {gamma theta : Real} (hg : 0 < gamma) (ht : 0 < theta)
    (hu2 : 2 ≤ 2 / (gamma * theta)) :
    ((2 / (gamma * theta)) ^ 2)⁻¹ ≤ theta * gamma / 4 := by
  have hgt : 0 < gamma * theta := mul_pos hg ht
  have heq : theta * gamma / 4 = (2 * (2 / (gamma * theta)))⁻¹ := by
    field_simp; ring
  rw [heq]
  exact inv_anti₀ (by positivity) (by nlinarith)

theorem polyPieceBudget_ge_power {gamma theta : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) :
    ((2 / (gamma * theta)) ^ ((2 : Nat) ^ 69))⁻¹ ≤ polyPieceBudget theta gamma := by
  obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  have hq := quarter_prod_ge_inv_sq hg ht hu2
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
  -- θ₁ ≥ u^(-2^65)
  have hθ1 : (u ^ ((2 : Nat) ^ 65))⁻¹ ≤ section16ThetaOne theta gamma 1 := by
    unfold section16ThetaOne
    have h := pow_le_pow_left₀ (by positivity) hq ((2 : Nat) ^ ((2 : Nat) ^ (1 + 5)))
    rw [inv_pow, ← pow_mul] at h
    refine le_trans ?_ h
    apply inv_anti₀ (pow_pos hupos _)
    apply pow_le_pow_right₀ hu1
    norm_num
  have hθ18 : (u ^ ((2 : Nat) ^ 68))⁻¹ ≤ section16ThetaOne theta gamma 1 ^ 8 := by
    have h := pow_le_pow_left₀ (inv_nonneg.mpr (pow_pos hupos _).le) hθ1 8
    rw [inv_pow, ← pow_mul] at h
    refine le_trans ?_ h
    apply inv_anti₀ (pow_pos hupos _)
    apply pow_le_pow_right₀ hu1
    norm_num
  unfold polyPieceBudget section16ThetaTwo
  calc (u ^ ((2 : Nat) ^ 69))⁻¹ ≤ (u ^ 35 * u ^ ((2 : Nat) ^ 68))⁻¹ := by
        apply inv_anti₀ (mul_pos (pow_pos hupos _) (pow_pos hupos _))
        rw [← pow_add]
        apply pow_le_pow_right₀ hu1
        norm_num
    _ = (u ^ 35)⁻¹ * (u ^ ((2 : Nat) ^ 68))⁻¹ := mul_inv _ _
    _ ≤ (2 : Real) ^ (-(32 : Real)) / 8 * section16ThetaOne theta gamma 1 ^ 8 :=
        mul_le_mul h35 hθ18 (inv_nonneg.mpr (pow_pos hupos _).le) (by positivity)
    _ = (2 : Real) ^ (-(32 : Real)) * section16ThetaOne theta gamma 1 ^ 8 / 8 := by ring

theorem polyPieceBudget_pos_le {gamma theta : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) :
    0 < polyPieceBudget theta gamma ∧ polyPieceBudget theta gamma ≤ 1 := by
  obtain ⟨h1, h2⟩ := section16ThetaTwo_pos_le (gamma := gamma) 1 ht ht1 hg hg1
  unfold polyPieceBudget
  exact ⟨by positivity, by linarith⟩

/-- `θ′⁻¹ ≤ (2/(γθ))^(2^69)` for the piece budget `θ′`. -/
theorem polyPieceBudget_inv_le_power {gamma theta : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) :
    (polyPieceBudget theta gamma)⁻¹ ≤ (2 / (gamma * theta)) ^ ((2 : Nat) ^ 69) := by
  obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  have hupos : 0 < 2 / (gamma * theta) := by linarith
  have h := polyPieceBudget_ge_power hg hg1 ht ht1
  have := inv_anti₀ (inv_pos.mpr (pow_pos hupos _)) h
  rwa [inv_inv] at this

/-- The face and slice count `q(γ, θ′) ≤ (2/(γθ))^(2^84)`. -/
theorem polyPieceFaceCount_le_power {gamma theta : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) :
    (polyPieceFaceCount theta gamma : Real) ≤ (2 / (gamma * theta)) ^ ((2 : Nat) ^ 84) := by
  obtain ⟨hu2, -, h2g, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  obtain ⟨hb, hb1⟩ := polyPieceBudget_pos_le hg hg1 ht ht1
  have hbinv := polyPieceBudget_inv_le_power hg hg1 ht ht1
  have hBF := section16BaseFamilyBound_le_power hg hg1 hb hb1
  set u := 2 / (gamma * theta) with hu
  clear_value u
  have hu1 : 1 ≤ u := le_trans (by norm_num) hu2
  have hupos : 0 < u := lt_of_lt_of_le (by norm_num) hu2
  have hbase : 2 / (gamma * polyPieceBudget theta gamma) ≤ u ^ ((2 : Nat) ^ 69 + 1) := by
    rw [show 2 / (gamma * polyPieceBudget theta gamma) =
      2 / gamma * (polyPieceBudget theta gamma)⁻¹ by field_simp]
    rw [pow_succ, mul_comm (u ^ _) u]
    exact mul_le_mul h2g hbinv (inv_pos.mpr hb).le hupos.le
  unfold polyPieceFaceCount
  refine hBF.trans ?_
  calc (2 / (gamma * polyPieceBudget theta gamma)) ^ ((2 : Nat) ^ 14)
      ≤ (u ^ ((2 : Nat) ^ 69 + 1)) ^ ((2 : Nat) ^ 14) :=
        pow_le_pow_left₀ (div_pos (by norm_num) (mul_pos hg hb)).le hbase _
    _ = u ^ (((2 : Nat) ^ 69 + 1) * (2 : Nat) ^ 14) := (pow_mul _ _ _).symm
    _ ≤ u ^ ((2 : Nat) ^ 84) := pow_le_pow_right₀ hu1 (by norm_num)

/-- The number of pieces `⌊γ⁻²/(5θ′)⌋ ≤ (2/(γθ))^(2^70)`. -/
theorem polyTwoPieces_le_power {gamma theta : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) :
    (polyTwoPieces gamma theta : Real) ≤ (2 / (gamma * theta)) ^ ((2 : Nat) ^ 70) := by
  obtain ⟨hu2, hginv, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  obtain ⟨hb, hb1⟩ := polyPieceBudget_pos_le hg hg1 ht ht1
  have hb5 : (5 * polyPieceBudget theta gamma)⁻¹ ≤ (polyPieceBudget theta gamma)⁻¹ :=
    inv_anti₀ hb (by linarith)
  have hbinv := polyPieceBudget_inv_le_power hg hg1 ht ht1
  set u := 2 / (gamma * theta) with hu
  clear_value u
  have hu1 : 1 ≤ u := le_trans (by norm_num) hu2
  have hupos : 0 < u := lt_of_lt_of_le (by norm_num) hu2
  have hg2 : gamma ^ (-(2 : Int)) ≤ u ^ 2 := by
    rw [zpow_neg, zpow_ofNat, ← inv_pow]
    exact pow_le_pow_left₀ (inv_pos.mpr hg).le hginv 2
  have hgz : 0 ≤ gamma ^ (-(2 : Int)) := zpow_nonneg hg.le _
  unfold polyTwoPieces
  refine (Nat.floor_le (div_nonneg hgz (by positivity))).trans ?_
  calc gamma ^ (-(2 : Int)) / (5 * polyPieceBudget theta gamma)
      ≤ gamma ^ (-(2 : Int)) * (polyPieceBudget theta gamma)⁻¹ := by
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left hb5 hgz
    _ ≤ u ^ 2 * u ^ ((2 : Nat) ^ 69) :=
        mul_le_mul hg2 hbinv (inv_pos.mpr hb).le (pow_pos hupos _).le
    _ = u ^ (2 + (2 : Nat) ^ 69) := (pow_add _ _ _).symm
    _ ≤ u ^ ((2 : Nat) ^ 70) := pow_le_pow_right₀ hu1 (by norm_num)

/-! ### Lemma 15.6's threshold -/

theorem lemma156ExplicitThreshold_one_le_power {gamma theta : Real} (hg : 0 < gamma)
    (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1) :
    lemma156ExplicitThreshold 1 (theta / 2) gamma ≤ (2 / (gamma * theta)) ^ ((2 : Nat) ^ 45) := by
  obtain ⟨hu2, -, -, h1, h2⟩ := prod_scale_basic hg hg1 ht ht1
  set u := 2 / (gamma * theta) with hu
  clear_value u
  have hu1 : 1 ≤ u := le_trans (by norm_num) hu2
  have hupos : 0 < u := lt_of_lt_of_le (by norm_num) hu2
  have hu3 : (3 : Real) ≤ u ^ 2 := by nlinarith
  have hu4 : (u ^ 2)⁻¹ ≤ 1 / 4 := by
    rw [one_div]; exact inv_anti₀ (by norm_num) (by nlinarith)
  have heta : ((2 : Real)⁻¹ ^ 44) = ((2 : Real) ^ 44)⁻¹ := by rw [inv_pow]
  have h12 : (1 : Real) / 4 ≤ (1 - (2 : Real)⁻¹ ^ 44) / 2 := by rw [heta]; norm_num
  have heta0 : 0 ≤ (1 - (2 : Real)⁻¹ ^ 44) / 2 := by rw [heta]; norm_num
  have h46 : ((2 : Real) ^ 46)⁻¹ ≤ (2 : Real)⁻¹ ^ 44 / 4 := by rw [heta]; norm_num
  have h46u : (u ^ 46)⁻¹ ≤ ((2 : Real) ^ 46)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_left₀ (by norm_num) hu2 46)
  have h51 : (3 : Real) ^ (16 * 2 ^ 1) * 1 ≤ u ^ 51 :=
    (show (3 : Real) ^ (16 * 2 ^ 1) * 1 ≤ (2 : Real) ^ 51 by norm_num).trans
      (pow_le_pow_left₀ (by norm_num) hu2 51)
  -- the selection base `a = (θ/2)^112 γ^336 ≥ u^(-448)`
  have hbase : (u ^ 448)⁻¹ ≤ (theta / 2) ^ (7 * 4 ^ (1 + 1)) * gamma ^ (21 * 1 * 4 ^ (1 + 1)) := by
    have hp1 := pow_le_pow_left₀ (inv_pos.mpr hupos).le h1 (7 * 4 ^ (1 + 1))
    have hp2 := pow_le_pow_left₀ (inv_pos.mpr hupos).le h2 (21 * 1 * 4 ^ (1 + 1))
    calc (u ^ 448)⁻¹ = u⁻¹ ^ (7 * 4 ^ (1 + 1)) * u⁻¹ ^ (21 * 1 * 4 ^ (1 + 1)) := by
          rw [← pow_add, inv_pow]; norm_num
      _ ≤ _ := mul_le_mul hp1 hp2 (by positivity) (by positivity)
  set a := (theta / 2) ^ (7 * 4 ^ (1 + 1)) * gamma ^ (21 * 1 * 4 ^ (1 + 1)) with ha
  have hapos : 0 < a := lt_of_lt_of_le (by positivity) hbase
  have hb : (u ^ 494)⁻¹ ≤ a * (2 : Real)⁻¹ ^ 44 / 4 := by
    calc (u ^ 494)⁻¹ = (u ^ 448)⁻¹ * (u ^ 46)⁻¹ := by rw [← mul_inv, ← pow_add]
      _ ≤ a * ((2 : Real)⁻¹ ^ 44 / 4) :=
          mul_le_mul hbase (h46u.trans h46) (by positivity) hapos.le
      _ = a * (2 : Real)⁻¹ ^ 44 / 4 := by ring
  set E := arrangementSelectionExponent 1 with hE
  have hEval : E = (2 : Nat) ^ 36 := by rw [hE]; unfold arrangementSelectionExponent; norm_num
  -- from here on the context carries exponents beyond `2^24`: no `linarith`
  have hsel : (u ^ (494 * (2 : Nat) ^ 36))⁻¹ ≤ (a * (2 : Real)⁻¹ ^ 44 / 4) ^ E := by
    rw [hEval]
    have h := pow_le_pow_left₀ (inv_pos.mpr (pow_pos hupos _)).le hb ((2 : Nat) ^ 36)
    rw [inv_pow, ← pow_mul] at h
    exact h
  have hden : (u ^ (494 * (2 : Nat) ^ 36 + 2))⁻¹ ≤
      (1 - (2 : Real)⁻¹ ^ 44) * (a * (2 : Real)⁻¹ ^ 44 / 4) ^ E / 2 * 1 := by
    calc (u ^ (494 * (2 : Nat) ^ 36 + 2))⁻¹ = (u ^ 2)⁻¹ * (u ^ (494 * (2 : Nat) ^ 36))⁻¹ := by
          rw [← mul_inv, ← pow_add, add_comm]
      _ ≤ (1 - (2 : Real)⁻¹ ^ 44) / 2 * (a * (2 : Real)⁻¹ ^ 44 / 4) ^ E :=
          mul_le_mul (hu4.trans h12) hsel (inv_pos.mpr (pow_pos hupos _)).le heta0
      _ = (1 - (2 : Real)⁻¹ ^ 44) * (a * (2 : Real)⁻¹ ^ 44 / 4) ^ E / 2 * 1 := by ring
  have hdenpos : 0 < (1 - (2 : Real)⁻¹ ^ 44) * (a * (2 : Real)⁻¹ ^ 44 / 4) ^ E / 2 * 1 :=
    lt_of_lt_of_le (inv_pos.mpr (pow_pos hupos _)) hden
  have hkey : u ^ 51 ≤ u ^ ((2 : Nat) ^ 45) * (u ^ (494 * (2 : Nat) ^ 36 + 2))⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ (pow_pos hupos _), ← pow_add]
    exact pow_le_pow_right₀ hu1 (by norm_num)
  unfold lemma156ExplicitThreshold
  rw [if_neg (by norm_num)]
  unfold selectionExplicitThreshold
  apply max_le
  · exact hu3.trans (pow_le_pow_right₀ hu1 (by norm_num))
  · rw [← hE, div_le_iff₀ hdenpos, Nat.cast_one]
    calc (3 : Real) ^ (16 * 2 ^ 1) * 1 ≤ u ^ 51 := h51
      _ ≤ u ^ ((2 : Nat) ^ 45) * (u ^ (494 * (2 : Nat) ^ 36 + 2))⁻¹ := hkey
      _ ≤ u ^ ((2 : Nat) ^ 45) *
          ((1 - (2 : Real)⁻¹ ^ 44) * (a * (2 : Real)⁻¹ ^ 44 / 4) ^ E / 2 * 1) :=
        mul_le_mul_of_nonneg_left hden (pow_pos hupos _).le

theorem polyTwoThreshold_le_power {gamma theta : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) :
    polyTwoThreshold theta gamma ≤ (2 / (gamma * theta)) ^ ((2 : Nat) ^ 45) := by
  obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  have hu3 : (3 : Real) ≤ (2 / (gamma * theta)) ^ 2 := by nlinarith
  unfold polyTwoThreshold
  apply max_le
  · exact hu3.trans (pow_le_pow_right₀ (by linarith) (by norm_num))
  · exact lemma156ExplicitThreshold_one_le_power hg hg1 ht ht1

/-! ### The family count

Below `w ≥ 2` is an abstract base; every count is bounded by `w^e` with an
explicit `e`, and only the power rules are used (no `linarith`, see the
trap above). -/

theorem le_pow_mono {w y : Real} {a b : Nat} (hw : 2 ≤ w) (hab : a ≤ b) (hy : y ≤ w ^ a) :
    y ≤ w ^ b :=
  hy.trans (pow_le_pow_right₀ (le_trans (by norm_num) hw) hab)

/-- A numerical constant `c ≤ 2^j` costs `j` in the exponent. -/
theorem const_mul_le_pow {w c y : Real} {a j : Nat} (hw : 2 ≤ w) (_hc0 : 0 ≤ c) (hc : c ≤ 2 ^ j)
    (hy0 : 0 ≤ y) (hy : y ≤ w ^ a) : c * y ≤ w ^ (j + a) := by
  rw [pow_add]
  exact mul_le_mul (hc.trans (pow_le_pow_left₀ (by norm_num) hw j)) hy hy0
    (pow_nonneg (le_trans (by norm_num) hw) _)

theorem nat_mul_le_pow {w : Real} {m n : Nat} {a b : Nat} (hw : 2 ≤ w) (hm : (m : Real) ≤ w ^ a)
    (hn : (n : Real) ≤ w ^ b) : ((m * n : Nat) : Real) ≤ w ^ (a + b) := by
  push_cast
  exact mul_le_pow_add (Nat.cast_nonneg _) (Nat.cast_nonneg _) hm hn (le_trans (by norm_num) hw)

/-- `c (m n + 1)` for a constant `c ≤ 2^j`. -/
theorem nat_affine_le_pow {w : Real} {c m n : Nat} {a b j : Nat} (hw : 2 ≤ w) (hc : (c : Real) ≤ 2 ^ j)
    (hm : (m : Real) ≤ w ^ a) (hn : (n : Real) ≤ w ^ b) :
    ((c * (m * n + 1) : Nat) : Real) ≤ w ^ (j + (a + b + 1)) := by
  have hmn := nat_mul_le_pow hw hm hn
  have h1 : (1 : Real) ≤ w ^ (a + b) := one_le_pow₀ (le_trans (by norm_num) hw)
  have hs : ((m * n + 1 : Nat) : Real) ≤ w ^ (a + b + 1) := by
    push_cast
    push_cast at hmn
    exact add_le_pow_succ hw hmn h1
  rw [Nat.cast_mul]
  exact const_mul_le_pow hw (Nat.cast_nonneg _) hc (Nat.cast_nonneg _) hs

theorem nat_max_one_le_pow {w : Real} {n a : Nat} (hw : 2 ≤ w) (hn : (n : Real) ≤ w ^ a) :
    ((max 1 n : Nat) : Real) ≤ w ^ a := by
  rw [Nat.cast_max, Nat.cast_one]
  exact max_le (one_le_pow₀ (le_trans (by norm_num) hw)) hn

/-- The sample count of the family piece cover. -/
theorem famPieceSamples_le_power {w rho : Real} {Qr : Real → Real} {n a b : Nat} (hw : 2 ≤ w)
    (hrho : 0 < rho) (hrw : rho⁻¹ ≤ w) (hQ : Qr (rho / 8) ≤ w ^ a) (hn : (n : Real) ≤ w ^ b) :
    (famPieceSamples Qr n rho : Real) ≤ w ^ (a + b + 7) := by
  have hw0 : 0 ≤ w := le_trans (by norm_num) hw
  have hQ1 : max 1 (Qr (rho / 8)) ≤ w ^ a := max_le (one_le_pow₀ (le_trans (by norm_num) hw)) hQ
  have hn1 := nat_max_one_le_pow hw hn
  have hQ0 : 0 ≤ max 1 (Qr (rho / 8)) := le_trans zero_le_one (le_max_left _ _)
  have hn0 : (0 : Real) ≤ ((max 1 n : Nat) : Real) := Nat.cast_nonneg _
  have hprod : max 1 (Qr (rho / 8)) * ((max 1 n : Nat) : Real) * rho⁻¹ ≤ w ^ (a + b + 1) :=
    mul_le_pow_add (mul_nonneg hQ0 hn0) (inv_pos.mpr hrho).le
      (mul_le_pow_add hQ0 hn0 hQ1 hn1 hw0) (by rw [pow_one]; exact hrw) hw0
  have hin : 6 * max 1 (Qr (rho / 8)) * ((max 1 n : Nat) : Real) / (rho / 4) ≤
      w ^ (5 + (a + b + 1)) := by
    rw [show 6 * max 1 (Qr (rho / 8)) * ((max 1 n : Nat) : Real) / (rho / 4) =
      24 * (max 1 (Qr (rho / 8)) * ((max 1 n : Nat) : Real) * rho⁻¹) by field_simp; ring]
    exact const_mul_le_pow hw (by norm_num) (by norm_num)
      (mul_nonneg (mul_nonneg hQ0 hn0) (inv_pos.mpr hrho).le) hprod
  have hin0 : 0 ≤ 6 * max 1 (Qr (rho / 8)) * ((max 1 n : Nat) : Real) / (rho / 4) := by
    positivity
  unfold famPieceSamples
  exact le_pow_mono hw (by omega) (ceil_le_pow_succ hw hin0 hin)

/-- The family graph count, from bounds on the samples, the slice count and `n`. -/
theorem famPieceGraphBound_le_power {w rho : Real} {Qr : Real → Real} {Pb : Nat → Real → Real}
    {n b s c : Nat} (hw : 2 ≤ w) (hn : (n : Real) ≤ w ^ b)
    (hS : (famPieceSamples Qr n rho : Real) ≤ w ^ s)
    (hP0 : 0 ≤ Pb (famPieceSamples Qr n rho) (rho / 4))
    (hP : Pb (famPieceSamples Qr n rho) (rho / 4) ≤ w ^ c) :
    famPieceGraphBound Qr Pb n rho ≤ w ^ (b + (2 * s + c + c)) := by
  have hw0 : 0 ≤ w := le_trans (by norm_num) hw
  set S := famPieceSamples Qr n rho
  set P := Pb S (rho / 4)
  have hC : ((S.choose 2 : Nat) : Real) ≤ w ^ (2 * s) := by
    have h1 : ((S.choose 2 : Nat) : Real) ≤ ((S ^ 2 : Nat) : Real) :=
      Nat.cast_le.mpr (Nat.choose_le_pow S 2)
    refine h1.trans ?_
    rw [Nat.cast_pow, mul_comm, pow_mul]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hS 2
  have hCPP : ((S.choose 2 : Nat) : Real) * P * P ≤ w ^ (2 * s + c + c) :=
    mul_le_pow_add (mul_nonneg (Nat.cast_nonneg _) hP0) hP0
      (mul_le_pow_add (Nat.cast_nonneg _) hP0 hC hP hw0) hP hw0
  have hmax : max P (((S.choose 2 : Nat) : Real) * P * P) ≤ w ^ (2 * s + c + c) :=
    max_le (le_pow_mono hw (by omega) hP) hCPP
  unfold famPieceGraphBound
  exact mul_le_pow_add (Nat.cast_nonneg _) (le_trans hP0 (le_max_left _ _)) hn hmax hw0

/-- `famTwoQr m q ≤ w^(a+b+5)`. -/
theorem famTwoQr_le_power {w : Real} {m q a b : Nat} (hw : 2 ≤ w) (hm : (m : Real) ≤ w ^ a)
    (hq : (q : Real) ≤ w ^ b) (t : Real) : famTwoQr m q t ≤ w ^ (a + b + 5) := by
  unfold famTwoQr
  apply max_le
  · exact le_pow_mono hw (by omega) (nat_affine_le_pow (c := 3) (j := 2) hw (by norm_num) hm hq)
  · exact le_pow_mono hw (by omega)
      (nat_affine_le_pow (c := 3 ^ (1 + 1)) (j := 4) hw (by norm_num) hm hq)

/-- `famTwoPb m q r ≤ w^(a+(s+b)+3)` for `r ≤ w^s`. -/
theorem famTwoPb_le_power {w : Real} {m q r a b s : Nat} (hw : 2 ≤ w) (hm : (m : Real) ≤ w ^ a)
    (hq : (q : Real) ≤ w ^ b) (hr : (r : Real) ≤ w ^ s) (t : Real) :
    famTwoPb m q r t ≤ w ^ (2 + (a + (s + b) + 1)) := by
  unfold famTwoPb
  exact nat_affine_le_pow (c := 3) (j := 2) hw (by norm_num) hm (nat_mul_le_pow hw hr hq)

/-- The family count of `PolyCoverAt 2`: `polyTwoFamCount θ γ ρ ≤ (2/(γθρ))^(2^89)`. -/
theorem polyTwoFamCount_le_power {gamma theta rho : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hr : 0 < rho) (hr1 : rho ≤ 1) :
    polyTwoFamCount theta gamma rho ≤ (2 / (gamma * theta * rho)) ^ ((2 : Nat) ^ 89) := by
  have hgt : 0 < gamma * theta := mul_pos hg ht
  have hgt1 : gamma * theta ≤ 1 := mul_le_one₀ hg1 ht.le ht1
  have hvw : 2 / (gamma * theta) ≤ 2 / (gamma * theta * rho) :=
    div_le_div_of_nonneg_left (by norm_num) (mul_pos hgt hr) (by nlinarith)
  have hrw : rho⁻¹ ≤ 2 / (gamma * theta * rho) := by
    rw [show 2 / (gamma * theta * rho) = 2 / (gamma * theta) * rho⁻¹ by field_simp]
    have h2 : (1 : Real) ≤ 2 / (gamma * theta) := by rw [le_div_iff₀ hgt]; linarith
    have := inv_pos.mpr hr
    nlinarith
  obtain ⟨hv2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  have hm := polyTwoPieces_le_power hg hg1 ht ht1
  have hq := polyPieceFaceCount_le_power hg hg1 ht ht1
  set v := 2 / (gamma * theta) with hv
  set w := 2 / (gamma * theta * rho) with hw
  clear_value v w
  have hw2 : 2 ≤ w := hv2.trans hvw
  have hv0 : 0 ≤ v := le_trans (by norm_num) hv2
  -- both counts below `w^(2^84)`
  have hm' : (polyTwoPieces gamma theta : Real) ≤ w ^ ((2 : Nat) ^ 84) :=
    le_pow_mono hw2 (by norm_num) (hm.trans (pow_le_pow_left₀ hv0 hvw _))
  have hq' : (polyPieceFaceCount theta gamma : Real) ≤ w ^ ((2 : Nat) ^ 84) :=
    hq.trans (pow_le_pow_left₀ hv0 hvw _)
  set m := polyTwoPieces gamma theta
  set ql := polyPieceFaceCount theta gamma
  have hQr := famTwoQr_le_power hw2 hm' hq' (rho / 8)
  have hS := famPieceSamples_le_power (Qr := famTwoQr m ql) hw2 hr hrw hQr hm'
  have hP := famTwoPb_le_power hw2 hm' hq' hS (rho / 4)
  have hP0 : 0 ≤ famTwoPb m ql (famPieceSamples (famTwoQr m ql) m rho) (rho / 4) := by
    unfold famTwoPb; exact Nat.cast_nonneg _
  have hG := famPieceGraphBound_le_power (Pb := famTwoPb m ql) hw2 hm' hS hP0 hP
  unfold polyTwoFamCount
  apply max_le
  · exact le_pow_mono hw2 (by norm_num) hG
  · have h9 : ((3 ^ (1 + 1) * m : Nat) : Real) ≤ w ^ (4 + (2 : Nat) ^ 84) := by
      rw [Nat.cast_mul]
      exact const_mul_le_pow hw2 (Nat.cast_nonneg _) (by norm_num) (Nat.cast_nonneg _) hm'
    exact le_pow_mono hw2 (by norm_num) h9

/-! ### The counts of the length-six route -/

/-- `polyTwoQb γ θ ρ ≤ (2/(γθρ))^(2^90)`. -/
theorem polyTwoQb_le_power {gamma theta rho : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hr : 0 < rho) (hr1 : rho ≤ 1) :
    polyTwoQb gamma theta rho ≤ (2 / (gamma * theta * rho)) ^ ((2 : Nat) ^ 90) := by
  have hgt : 0 < gamma * theta := mul_pos hg ht
  have hgt1 : gamma * theta ≤ 1 := mul_le_one₀ hg1 ht.le ht1
  have hvw : 2 / (gamma * theta) ≤ 2 / (gamma * theta * rho) :=
    div_le_div_of_nonneg_left (by norm_num) (mul_pos hgt hr) (by nlinarith)
  obtain ⟨hv2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  have hthr3 : (3 : Real) ≤ polyTwoThreshold theta gamma := by
    unfold polyTwoThreshold; exact le_max_left _ _
  have hthr := polyTwoThreshold_le_power hg hg1 ht ht1
  have hfam := polyTwoFamCount_le_power hg hg1 ht ht1 hr hr1
  set v := 2 / (gamma * theta) with hv
  set w := 2 / (gamma * theta * rho) with hw
  clear_value v w
  have hw2 : 2 ≤ w := hv2.trans hvw
  have hv0 : 0 ≤ v := le_trans (by norm_num) hv2
  have hthr' : polyTwoThreshold theta gamma ≤ w ^ ((2 : Nat) ^ 45) :=
    hthr.trans (pow_le_pow_left₀ hv0 hvw _)
  have hceil := ceil_le_pow_succ hw2 (le_trans (by norm_num) hthr3) hthr'
  unfold polyTwoQb
  apply max_le
  · exact le_pow_mono hw2 (by norm_num) hfam
  · rw [Nat.cast_mul]
    exact le_pow_mono hw2 (by norm_num)
      (const_mul_le_pow (j := 4) hw2 (Nat.cast_nonneg _) (by norm_num) (Nat.cast_nonneg _) hceil)

/-- **The counts of the length-six route are polynomial**:
`sixQb l γ θ ρ ≤ (2/(γθρ))^(2^90)` for `γ, θ, ρ ∈ (0, 1]`. -/
theorem sixQb_le_power (l : Nat) {gamma theta rho : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hr : 0 < rho) (hr1 : rho ≤ 1) :
    sixQb l gamma theta rho ≤ (2 / (gamma * theta * rho)) ^ ((2 : Nat) ^ 90) := by
  unfold sixQb
  split_ifs
  · have hgt : 0 < gamma * theta := mul_pos hg ht
    have hgt1 : gamma * theta ≤ 1 := mul_le_one₀ hg1 ht.le ht1
    have hvw : 2 / (gamma * theta) ≤ 2 / (gamma * theta * rho) :=
      div_le_div_of_nonneg_left (by norm_num) (mul_pos hgt hr) (by nlinarith)
    obtain ⟨hv2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
    have hB := section16BaseFamilyBound_le_power hg hg1 ht ht1
    set v := 2 / (gamma * theta) with hv
    set w := 2 / (gamma * theta * rho) with hw
    clear_value v w
    have hw2 : 2 ≤ w := hv2.trans hvw
    have hv0 : 0 ≤ v := le_trans (by norm_num) hv2
    have hB' : (section16BaseFamilyBound gamma theta : Real) ≤ w ^ ((2 : Nat) ^ 14) :=
      hB.trans (pow_le_pow_left₀ hv0 hvw _)
    show ((3 * section16BaseFamilyBound gamma theta : Nat) : Real) ≤ _
    rw [Nat.cast_mul]
    exact le_pow_mono hw2 (by norm_num)
      (const_mul_le_pow (j := 2) hw2 (Nat.cast_nonneg _) (by norm_num) (Nat.cast_nonneg _) hB')
  · exact polyTwoQb_le_power hg hg1 ht ht1 hr hr1
end LeanProofs.GowersSzemeredi
