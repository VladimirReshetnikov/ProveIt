import GowersSzemeredi.Proofs18LengthSixCounts
import GowersSzemeredi.Proofs16PolyCoverTwoSide
import GowersSzemeredi.Proofs18LengthSixRoute

/-! Declarations of `Proofs18LengthSixCounts` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

section
open BaseCase

theorem polyPieceBudget_pos_le {gamma theta : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) :
    0 < polyPieceBudget theta gamma ∧ polyPieceBudget theta gamma ≤ 1 := by
  obtain ⟨h1, h2⟩ := section16ThetaTwo_pos_le (gamma := gamma) 1 ht ht1 hg hg1
  unfold polyPieceBudget
  exact ⟨by positivity, by linarith⟩

/-- The face and slice count `q(γ, θ′) ≤ (2/(γθ))^(2^84)`. -/
theorem polyPieceFaceCount_le_power {gamma theta : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) :
    (polyPieceFaceCount theta gamma : Real) ≤ (2 / (gamma * theta)) ^ ((2 : Nat) ^ 84) := by
  obtain ⟨hu2, -, h2g, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  obtain ⟨hb, hb1⟩ := polyPieceBudget_pos_le hg hg1 ht ht1
  have hbinv := polyPieceBudget_inv_le_power hg hg1 ht ht1
  have hBF := section16BaseFamilyBound_le_dyadic_power hg hg1 hb hb1
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
  obtain ⟨hb, _⟩ := polyPieceBudget_pos_le hg hg1 ht ht1
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

/-- A reciprocal-power lower bound on the selection density bounds Lemma 15.6's
threshold. The constants 46 and 2 absorb the fixed selection margin. -/
theorem lemma156ExplicitThreshold_le_power_of_selection_base
    {beta gamma u : Real} {k c p : Nat} (hk : 1 ≤ k) (hu : 2 ≤ u)
    (hbase : (u ^ c)⁻¹ ≤ beta ^ (7 * 4 ^ (k + 1)) * gamma ^ (21 * k * 4 ^ (k + 1)))
    (hdegree : 32 * 2 ^ k + k + ((c + 46) * arrangementSelectionExponent k + 2) ≤ p) :
    lemma156ExplicitThreshold k beta gamma ≤ u ^ p := by
  have hu1 : 1 ≤ u := le_trans (by norm_num) hu
  have hupos : 0 < u := lt_of_lt_of_le (by norm_num) hu
  have hu3 : (3 : Real) ≤ u ^ 2 := by nlinarith only [hu]
  have hu4 : (u ^ 2)⁻¹ ≤ 1 / 4 := by
    rw [one_div]; exact inv_anti₀ (by norm_num) (by nlinarith only [hu])
  have heta : ((2 : Real)⁻¹ ^ 44) = ((2 : Real) ^ 44)⁻¹ := by rw [inv_pow]
  have h12 : (1 : Real) / 4 ≤ (1 - (2 : Real)⁻¹ ^ 44) / 2 := by rw [heta]; norm_num
  have heta0 : 0 ≤ (1 - (2 : Real)⁻¹ ^ 44) / 2 := by rw [heta]; norm_num
  have h46 : ((2 : Real) ^ 46)⁻¹ ≤ (2 : Real)⁻¹ ^ 44 / 4 := by rw [heta]; norm_num
  have h46u : (u ^ 46)⁻¹ ≤ ((2 : Real) ^ 46)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_left₀ (by norm_num) hu 46)
  have hC : (3 : Real) ^ (16 * 2 ^ k) * (k : Real) ≤ u ^ (32 * 2 ^ k + k) := by
    have h3 : (3 : Real) ^ (16 * 2 ^ k) ≤ u ^ (32 * 2 ^ k) := by
      rw [show 32 * 2 ^ k = 2 * (16 * 2 ^ k) by ring, pow_mul u 2 (16 * 2 ^ k)]
      exact pow_le_pow_left₀ (by norm_num) hu3 _
    have hkk : (k : Real) ≤ u ^ k := by
      have hk2 : (k : Real) ≤ 2 ^ k := by exact_mod_cast (Nat.lt_two_pow_self (n := k)).le
      exact hk2.trans (pow_le_pow_left₀ (by norm_num) hu k)
    rw [pow_add]
    exact mul_le_mul h3 hkk (Nat.cast_nonneg _) (pow_nonneg hupos.le _)
  set a := beta ^ (7 * 4 ^ (k + 1)) * gamma ^ (21 * k * 4 ^ (k + 1))
  have hapos : 0 < a := lt_of_lt_of_le (by positivity) hbase
  have hb : (u ^ (c + 46))⁻¹ ≤ a * (2 : Real)⁻¹ ^ 44 / 4 := by
    calc (u ^ (c + 46))⁻¹ = (u ^ c)⁻¹ * (u ^ 46)⁻¹ := by rw [← mul_inv, ← pow_add]
      _ ≤ a * ((2 : Real)⁻¹ ^ 44 / 4) :=
          mul_le_mul hbase (h46u.trans h46) (by positivity) hapos.le
      _ = a * (2 : Real)⁻¹ ^ 44 / 4 := by ring
  set E := arrangementSelectionExponent k with hE
  have hsel : (u ^ ((c + 46) * E))⁻¹ ≤ (a * (2 : Real)⁻¹ ^ 44 / 4) ^ E := by
    have h := pow_le_pow_left₀ (inv_pos.mpr (pow_pos hupos _)).le hb E
    rw [inv_pow, ← pow_mul] at h
    exact h
  have hden : (u ^ ((c + 46) * E + 2))⁻¹ ≤
      (1 - (2 : Real)⁻¹ ^ 44) * (a * (2 : Real)⁻¹ ^ 44 / 4) ^ E / 2 * 1 := by
    calc (u ^ ((c + 46) * E + 2))⁻¹ = (u ^ 2)⁻¹ * (u ^ ((c + 46) * E))⁻¹ := by
          rw [← mul_inv, ← pow_add, add_comm]
      _ ≤ (1 - (2 : Real)⁻¹ ^ 44) / 2 * (a * (2 : Real)⁻¹ ^ 44 / 4) ^ E :=
          mul_le_mul (hu4.trans h12) hsel (inv_pos.mpr (pow_pos hupos _)).le heta0
      _ = (1 - (2 : Real)⁻¹ ^ 44) * (a * (2 : Real)⁻¹ ^ 44 / 4) ^ E / 2 * 1 := by ring
  have hdenpos : 0 < (1 - (2 : Real)⁻¹ ^ 44) * (a * (2 : Real)⁻¹ ^ 44 / 4) ^ E / 2 * 1 :=
    lt_of_lt_of_le (inv_pos.mpr (pow_pos hupos _)) hden
  have hkey : u ^ (32 * 2 ^ k + k) ≤ u ^ p * (u ^ ((c + 46) * E + 2))⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ (pow_pos hupos _), ← pow_add]
    exact pow_le_pow_right₀ hu1 hdegree
  unfold lemma156ExplicitThreshold
  rw [if_neg (by omega)]
  unfold selectionExplicitThreshold
  apply max_le
  · exact hu3.trans (pow_le_pow_right₀ hu1 (by omega))
  · rw [← hE, div_le_iff₀ hdenpos]
    exact hC.trans (hkey.trans (mul_le_mul_of_nonneg_left hden (pow_pos hupos _).le))

theorem lemma156ExplicitThreshold_one_le_power {gamma theta : Real} (hg : 0 < gamma)
    (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1) :
    lemma156ExplicitThreshold 1 (theta / 2) gamma ≤ (2 / (gamma * theta)) ^ ((2 : Nat) ^ 45) := by
  obtain ⟨hu2, -, -, h1, h2⟩ := prod_scale_basic hg hg1 ht ht1
  set u := 2 / (gamma * theta) with hu
  clear_value u
  have hupos : 0 < u := lt_of_lt_of_le (by norm_num) hu2
  have hbase : (u ^ 448)⁻¹ ≤ (theta / 2) ^ (7 * 4 ^ (1 + 1)) * gamma ^ (21 * 1 * 4 ^ (1 + 1)) := by
    have hp1 := pow_le_pow_left₀ (inv_pos.mpr hupos).le h1 (7 * 4 ^ (1 + 1))
    have hp2 := pow_le_pow_left₀ (inv_pos.mpr hupos).le h2 (21 * 1 * 4 ^ (1 + 1))
    calc (u ^ 448)⁻¹ = u⁻¹ ^ (7 * 4 ^ (1 + 1)) * u⁻¹ ^ (21 * 1 * 4 ^ (1 + 1)) := by
          rw [← pow_add, inv_pow]; norm_num
      _ ≤ _ := mul_le_mul hp1 hp2 (by positivity) (by positivity)
  exact lemma156ExplicitThreshold_le_power_of_selection_base (by norm_num) hu2 hbase
    (by norm_num [arrangementSelectionExponent])

theorem polyTwoThreshold_le_power {gamma theta : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) :
    polyTwoThreshold theta gamma ≤ (2 / (gamma * theta)) ^ ((2 : Nat) ^ 45) := by
  obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  have hu3 : (3 : Real) ≤ (2 / (gamma * theta)) ^ 2 := by nlinarith
  unfold polyTwoThreshold
  apply max_le
  · exact hu3.trans (pow_le_pow_right₀ (by linarith) (by norm_num))
  · exact lemma156ExplicitThreshold_one_le_power hg hg1 ht ht1

/-- The family count of `PolyCoverAt 2`: `polyTwoFamCount θ γ ρ ≤ (2/(γθρ))^(2^89)`. -/
theorem polyTwoFamCount_le_power {gamma theta rho : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hr : 0 < rho) (hr1 : rho ≤ 1) :
    polyTwoFamCount theta gamma rho ≤ (2 / (gamma * theta * rho)) ^ ((2 : Nat) ^ 89) := by
  obtain ⟨hv2, hvw, hrw⟩ := prod_scale_radius_bounds hg hg1 ht ht1 hr hr1
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
  unfold polyTwoFamCount
  exact le_pow_mono hw2 (by norm_num) (famTwoCount_le_power hw2 hr hrw hm' hq')

/-! ### The counts of the length-six route -/

/-- `polyTwoQb γ θ ρ ≤ (2/(γθρ))^(2^90)`. -/
theorem polyTwoQb_le_power {gamma theta rho : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hr : 0 < rho) (hr1 : rho ≤ 1) :
    polyTwoQb gamma theta rho ≤ (2 / (gamma * theta * rho)) ^ ((2 : Nat) ^ 90) := by
  obtain ⟨hv2, hvw, -⟩ := prod_scale_radius_bounds hg hg1 ht ht1 hr hr1
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
  · obtain ⟨hv2, hvw, -⟩ := prod_scale_radius_bounds hg hg1 ht ht1 hr hr1
    have hB := section16BaseFamilyBound_le_dyadic_power hg hg1 ht ht1
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

end

end LeanProofs.GowersSzemeredi
