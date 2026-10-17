import GowersSzemeredi.Proofs16ClassStepFejer
import GowersSzemeredi.Proofs16SplitFejerDegrees
import GowersSzemeredi.Proofs18FejerSeedCounts

/-! **The class-step bounds under the Fejér θ₁** (Notes L.16d).

The Fejér analogue of `Proofs16ClassStepBounds`, in the base
`u = 2/(γθ)`, with `F = fejerProductExponent k` in place of the printed
`2^(2^(k+5))`:

| quantity | printed | Fejér |
|---|---|---|
| `θ₁⁻¹` | `u^(2^(2^(k+5)+1))` | `u^(2F)` |
| class budget⁻¹ | `u^(2^(2^(k+5)+5))` | `u^(32F)` |
| `δ⁻¹` | `u^(2^(2^(k+5)+5))` | `u^(32F)` |
| pieces | `u^(stepP k)` | `u^(fejerStepP k)`, `fejerStepP k = 64F` |
| `ζ⁻¹` | `exp(u^(stepT k))` | `exp(u^(fejerStepT k))`, `fejerStepT k = 22F + 105` |
| Lemma 15.6 threshold | `u^(stepP k)` | `u^(fejerStepP k)` |

These are exactly the inputs of the class-step degrees, so
`Proofs16ClassStepDegreesFejer` is the corpus's degree computation with
`stepP`, `stepT` replaced by `fejerStepP`, `fejerStepT`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- `F ≥ 2^(4k+11)`. -/
theorem fejerProductExponent_ge (k : Nat) : 2 ^ (4 * k + 11) ≤ fejerProductExponent k := by
  unfold fejerProductExponent fejerSelectionExponent
  calc 2 ^ (4 * k + 11) = 2 ^ (3 * k + 7) * (2 ^ (k + 4) * 1) := by
        rw [mul_one, ← pow_add]; congr 1; omega
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))

theorem fejerThetaOne_inv_le_gen {gamma theta : Real} (k : Nat) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) :
    (fejerThetaOne theta gamma k)⁻¹ ≤ (2 / (gamma * theta)) ^ (2 * fejerProductExponent k) := by
  obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  have hq := quarter_prod_ge_inv_sq hg ht hu2
  set u := 2 / (gamma * theta) with hu
  clear_value u
  have hupos : 0 < u := lt_of_lt_of_le (by norm_num) hu2
  have hqi : (theta * gamma / 4)⁻¹ ≤ u ^ 2 := by
    have := inv_anti₀ (inv_pos.mpr (pow_pos hupos 2)) hq
    rwa [inv_inv] at this
  unfold fejerThetaOne
  rw [← inv_pow, pow_mul]
  exact pow_le_pow_left₀ (by positivity) hqi _

theorem classBudgetW_fejer_inv_le {gamma theta : Real} (k : Nat) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) :
    (classBudgetW (fejerThetaOne theta gamma k) k)⁻¹ ≤
      (2 / (gamma * theta)) ^ (32 * fejerProductExponent k) := by
  obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  obtain ⟨ha0, haS⟩ := fejerThetaOne_bounds k ht ht1 hg hg1
  have h0 : 0 < fejerThetaOne theta gamma k := by linarith
  have hθi := fejerThetaOne_inv_le_gen k hg hg1 ht ht1
  have hF := fejerProductExponent_ge k
  have hkF : k + 34 ≤ 16 * fejerProductExponent k := by
    have : k + 34 ≤ 2 ^ (4 * k + 11) := by
      have h1 := Nat.lt_two_pow_self (n := 4 * k + 11)
      have h2 : 2048 ≤ 2 ^ (4 * k + 11) :=
        le_trans (by norm_num) (Nat.pow_le_pow_right (n := 2) (by norm_num) (show 11 ≤ 4 * k + 11 by omega))
      omega
    omega
  have hval : (classBudgetW (fejerThetaOne theta gamma k) k)⁻¹ = 2 ^ (k + 2) *
      ((2 : Real) ^ (32 : Real) * ((fejerThetaOne theta gamma k)⁻¹) ^ 8) := by
    unfold classBudgetW section16ThetaTwo
    rw [Real.rpow_neg (by norm_num), inv_div, div_eq_mul_inv, mul_inv, inv_inv, inv_pow]
  rw [hval]
  set t := fejerThetaOne theta gamma k
  set F := fejerProductExponent k
  set u := 2 / (gamma * theta) with hu
  clear_value u t F
  have hupos : 0 < u := lt_of_lt_of_le (by norm_num) hu2
  have hu1 : 1 ≤ u := le_trans (by norm_num) hu2
  have h32 : (2 : Real) ^ (32 : Real) ≤ u ^ 32 := by
    rw [show (32 : Real) = ((32 : Nat) : Real) by norm_num, Real.rpow_natCast]
    exact pow_le_pow_left₀ (by norm_num) hu2 32
  have hk2 : (2 : Real) ^ (k + 2) ≤ u ^ (k + 2) := pow_le_pow_left₀ (by norm_num) hu2 _
  have ht8 : (t⁻¹) ^ 8 ≤ (u ^ (2 * F)) ^ 8 := pow_le_pow_left₀ (inv_pos.mpr h0).le hθi 8
  calc (2 : Real) ^ (k + 2) * ((2 : Real) ^ (32 : Real) * (t⁻¹) ^ 8)
      ≤ u ^ (k + 2) * (u ^ 32 * (u ^ (2 * F)) ^ 8) :=
        mul_le_mul hk2 (mul_le_mul h32 ht8 (by positivity) (pow_nonneg hupos.le _))
          (by positivity) (pow_nonneg hupos.le _)
    _ = u ^ (k + 34 + 16 * F) := by
        rw [← pow_mul, ← pow_add, ← pow_add]
        congr 1
        ring
    _ ≤ u ^ (32 * F) := pow_le_pow_right₀ hu1 (by omega)

theorem classDeltaW_fejer_inv_le {gamma theta : Real} (k : Nat) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) :
    (section16Delta (fejerThetaOne theta gamma k))⁻¹ ≤
      (2 / (gamma * theta)) ^ (32 * fejerProductExponent k) := by
  obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  obtain ⟨ha0, haS⟩ := fejerThetaOne_bounds k ht ht1 hg hg1
  obtain ⟨h0, h1, -, -⟩ := section16_theta_delta_bounds_with ha0 haS
  have hθi := fejerThetaOne_inv_le_gen k hg hg1 ht ht1
  have hF := fejerProductExponent_ge k
  have hF49 : 37 + (2 * fejerProductExponent k + 2) * 6 ≤ 32 * fejerProductExponent k := by
    have : 49 ≤ 2 ^ (4 * k + 11) :=
      le_trans (by norm_num) (Nat.pow_le_pow_right (n := 2) (by norm_num) (show 11 ≤ 4 * k + 11 by omega))
    omega
  set t := fejerThetaOne theta gamma k
  set F := fejerProductExponent k
  set u := 2 / (gamma * theta) with hu
  clear_value u t F
  have hupos : 0 < u := lt_of_lt_of_le (by norm_num) hu2
  have hu1 : 1 ≤ u := le_trans (by norm_num) hu2
  have h4t : 4 / t ≤ u ^ (2 * F + 2) := by
    rw [div_eq_mul_inv, pow_add, mul_comm]
    exact mul_le_mul hθi (show (4 : Real) ≤ u ^ 2 by nlinarith only [hu2]) (by norm_num)
      (pow_nonneg hupos.le _)
  have h4t1 : 1 ≤ 4 / t := by rw [le_div_iff₀ h0]; linarith only [h1]
  have hval : (section16Delta t)⁻¹ = (2 : Real) ^ (37 : Real) * (4 / t) ^ ((11 : Real) / 2) := by
    unfold section16Delta
    rw [mul_inv, Real.rpow_neg (by norm_num), inv_inv, ← Real.inv_rpow (by positivity), inv_div]
  rw [hval]
  have h37 : (2 : Real) ^ (37 : Real) ≤ u ^ 37 := by
    rw [show (37 : Real) = ((37 : Nat) : Real) by norm_num, Real.rpow_natCast]
    exact pow_le_pow_left₀ (by norm_num) hu2 37
  have h6 : (4 / t) ^ ((11 : Real) / 2) ≤ (4 / t) ^ 6 := by
    rw [show (4 / t) ^ 6 = (4 / t) ^ ((6 : Nat) : Real) by rw [Real.rpow_natCast]]
    exact Real.rpow_le_rpow_of_exponent_le h4t1 (by norm_num)
  calc (2 : Real) ^ (37 : Real) * (4 / t) ^ ((11 : Real) / 2)
      ≤ u ^ 37 * (u ^ (2 * F + 2)) ^ 6 :=
        mul_le_mul h37 (h6.trans (pow_le_pow_left₀ (by positivity) h4t 6))
          (Real.rpow_nonneg (by positivity) _) (pow_nonneg hupos.le _)
    _ = u ^ (37 + (2 * F + 2) * 6) := by rw [← pow_mul, ← pow_add]
    _ ≤ u ^ (32 * F) := pow_le_pow_right₀ hu1 hF49

theorem classPiecesFejer_le_gen {gamma theta : Real} (k : Nat) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) :
    (classPiecesFejer gamma theta k : Real) ≤ (2 / (gamma * theta)) ^ fejerStepP k := by
  obtain ⟨hu2, hginv, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  obtain ⟨ha0, haS⟩ := fejerThetaOne_bounds k ht ht1 hg hg1
  obtain ⟨hb, _⟩ := classBudgetW_pos_le k ha0 haS
  have hbi := classBudgetW_fejer_inv_le k hg hg1 ht ht1
  have hF := fejerProductExponent_ge k
  have hstep : 2 + 32 * fejerProductExponent k ≤ fejerStepP k := by
    unfold fejerStepP
    have : 2 ≤ 2 ^ (4 * k + 11) :=
      le_trans (by norm_num) (Nat.pow_le_pow_right (n := 2) (by norm_num) (show 1 ≤ 4 * k + 11 by omega))
    omega
  set u := 2 / (gamma * theta) with hu
  clear_value u
  have hu1 : 1 ≤ u := le_trans (by norm_num) hu2
  have hupos : 0 < u := lt_of_lt_of_le (by norm_num) hu2
  have hg2 : gamma ^ (-(2 : Int)) ≤ u ^ 2 := by
    rw [zpow_neg, zpow_ofNat, ← inv_pow]
    exact pow_le_pow_left₀ (inv_pos.mpr hg).le hginv 2
  have hgz : 0 ≤ gamma ^ (-(2 : Int)) := zpow_nonneg hg.le _
  unfold classPiecesFejer
  refine (Nat.floor_le (div_nonneg hgz hb.le)).trans ?_
  calc gamma ^ (-(2 : Int)) / classBudgetW (fejerThetaOne theta gamma k) k
      = gamma ^ (-(2 : Int)) * (classBudgetW (fejerThetaOne theta gamma k) k)⁻¹ := div_eq_mul_inv _ _
    _ ≤ u ^ 2 * u ^ (32 * fejerProductExponent k) :=
        mul_le_mul hg2 hbi (inv_pos.mpr hb).le (pow_pos hupos _).le
    _ = u ^ (2 + 32 * fejerProductExponent k) := (pow_add _ _ _).symm
    _ ≤ u ^ fejerStepP k := pow_le_pow_right₀ hu1 hstep

/-- The exponent arithmetic of the Fejér threshold: with
`a = (7 + 21k)·4^(k+1) + k + 52`, `1 + k + (2a+1)·2^(k+4) ≤ 64·F`. -/
theorem fejer_threshold_exponent_le (k : Nat) :
    1 + k + (2 * (7 * 4 ^ (k + 1) + 21 * k * 4 ^ (k + 1) + k + 52) + 1) * 2 ^ (k + 4) ≤
      fejerStepP k := by
  unfold fejerStepP fejerProductExponent fejerSelectionExponent
  have e4 : 4 ^ (k + 1) = 4 * (2 ^ k * 2 ^ k) := by
    rw [pow_succ, show (4 : Nat) = 2 ^ 2 by norm_num, ← pow_mul, show 2 * k = k + k by ring, pow_add]
    ring
  have e16 : 2 ^ (k + 4) = 16 * 2 ^ k := by rw [pow_add]; ring
  have e128 : 2 ^ (3 * k + 7) = 128 * (2 ^ k * 2 ^ k * 2 ^ k) := by
    rw [show 3 * k + 7 = k + k + k + 7 by ring, pow_add, pow_add, pow_add]; ring
  rw [e4, e16, e128]
  have hkX : k ≤ 2 ^ k := (Nat.lt_two_pow_self).le
  have hX1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  generalize 2 ^ k = X at *
  have hX2 : 1 ≤ X * X := Nat.mul_le_mul hX1 hX1
  have hX3 : 1 ≤ X * X * X := Nat.mul_le_mul hX2 hX1
  have hkX3 : k * (X * X) ≤ X * X * X := by
    calc k * (X * X) ≤ X * (X * X) := Nat.mul_le_mul_right _ hkX
      _ = X * X * X := by ring
  nlinarith [Nat.mul_le_mul_left (X * X * X) hX1, Nat.mul_le_mul_left X hX3,
    Nat.mul_le_mul_left (X * X) hX2, Nat.mul_le_mul_right X hkX3]

/-- **The Fejér Lemma 15.6 threshold in dimension `k`** is at most
`u^(fejerStepP k)`, the slot of the printed `lemma156ExplicitThreshold_le_gen`. -/
theorem fejerProductThreshold_le_gen {gamma theta : Real} {k : Nat} (hk : 1 ≤ k)
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1) :
    fejerProductThreshold k (theta / 2) gamma ≤ (2 / (gamma * theta)) ^ fejerStepP k := by
  obtain ⟨hu2, -, -, h1, h2⟩ := prod_scale_basic hg hg1 ht ht1
  have hexp := fejer_threshold_exponent_le k
  set u := 2 / (gamma * theta) with hu
  clear_value u
  have hu1 : 1 ≤ u := le_trans (by norm_num) hu2
  have hupos : 0 < u := lt_of_lt_of_le (by norm_num) hu2
  set A : Nat := 7 * 4 ^ (k + 1) with hA
  set G : Nat := 21 * k * 4 ^ (k + 1) with hG
  have hbase : (u ^ (A + G))⁻¹ ≤ (theta / 2) ^ A * gamma ^ G := by
    have hp1 := pow_le_pow_left₀ (inv_pos.mpr hupos).le h1 A
    have hp2 := pow_le_pow_left₀ (inv_pos.mpr hupos).le h2 G
    calc (u ^ (A + G))⁻¹ = u⁻¹ ^ A * u⁻¹ ^ G := by rw [← pow_add, inv_pow]
      _ ≤ _ := mul_le_mul hp1 hp2 (by positivity) (by positivity)
  set a := (theta / 2) ^ A * gamma ^ G with ha
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
  have hae : (u ^ (A + G + 44))⁻¹ ≤ a * eta := by
    calc (u ^ (A + G + 44))⁻¹ = (u ^ (A + G))⁻¹ * (u ^ 44)⁻¹ := by rw [← mul_inv, ← pow_add]
      _ ≤ a * eta := mul_le_mul hbase h44 (by positivity) hapos.le
  have hsix : 6 / (min a 1 * eta) ≤ u ^ (A + G + 47) := by
    rw [hmin, div_le_iff₀ (mul_pos hapos heta0)]
    have h6 : (6 : Real) ≤ u ^ 3 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0:Real) ≤ 2) hu2 3]
    have hinv : 1 ≤ u ^ (A + G + 44) * (a * eta) := by
      have := mul_le_mul_of_nonneg_left hae (pow_pos hupos (A + G + 44)).le
      rwa [mul_inv_cancel₀ (pow_pos hupos _).ne'] at this
    calc (6 : Real) ≤ u ^ 3 * 1 := by rw [mul_one]; exact h6
      _ ≤ u ^ 3 * (u ^ (A + G + 44) * (a * eta)) := mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = u ^ (A + G + 47) * (a * eta) := by rw [← mul_assoc, ← pow_add]; ring_nf
  have hT : ((⌈6 / (min a 1 * eta)⌉₊ : Nat) : Real) ≤ u ^ (A + G + 47 + 1) :=
    ceil_le_pow_succ hu2 (by rw [hmin]; positivity) hsix
  have hT1 : 1 ≤ ⌈6 / (min a 1 * eta)⌉₊ := by
    rw [Nat.one_le_ceil_iff, hmin]; positivity
  set e : Nat := A + G + k + 52 with he
  have hm1 : ((fejerOrder k a eta : Nat) : Real) + 1 ≤ u ^ e := by
    unfold fejerOrder
    have hpos : 1 ≤ 2 ^ (k + 4) * ⌈6 / (min a 1 * eta)⌉₊ :=
      Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by positivity) (by omega))
    have hcast : ((2 ^ (k + 4) * ⌈6 / (min a 1 * eta)⌉₊ - 1 : Nat) : Real) + 1 =
        (2 : Real) ^ (k + 4) * ((⌈6 / (min a 1 * eta)⌉₊ : Nat) : Real) := by
      rw [Nat.cast_sub hpos]; push_cast; ring
    rw [hcast]
    calc (2 : Real) ^ (k + 4) * ((⌈6 / (min a 1 * eta)⌉₊ : Nat) : Real)
        ≤ u ^ (k + 4) * u ^ (A + G + 47 + 1) :=
          mul_le_mul (pow_le_pow_left₀ (by norm_num) hu2 _) hT (Nat.cast_nonneg _) (by positivity)
      _ = u ^ e := by rw [← pow_add, he]; ring_nf
  set m : Nat := fejerOrder k a eta with hmdef
  have hmpos : (0 : Real) < (m : Real) + 1 := by positivity
  have h2m : 2 * (m : Real) + 1 ≤ u ^ (e + 1) := by
    calc 2 * (m : Real) + 1 ≤ 2 * ((m : Real) + 1) := by linarith
      _ ≤ u * u ^ e := mul_le_mul hu2 hm1 hmpos.le hupos.le
      _ = u ^ (e + 1) := by rw [← pow_succ']
  have hkk : (k : Real) ≤ u ^ k := by
    have h := (Nat.lt_two_pow_self (n := k)).le
    calc (k : Real) ≤ (2 : Real) ^ k := by exact_mod_cast h
      _ ≤ u ^ k := pow_le_pow_left₀ (by norm_num) hu2 _
  have h16 : 2 * 8 * 2 ^ k = 2 ^ (k + 4) := by rw [pow_add]; ring
  have hc0 : fejerDegenerateConst k a eta ≤ u ^ ((e + 1) * 2 ^ (k + 4) + k) := by
    unfold fejerDegenerateConst
    rw [← hmdef, h16]
    have hp : (2 * (m : Real) + 1) ^ (2 ^ (k + 4)) ≤ u ^ ((e + 1) * 2 ^ (k + 4)) := by
      rw [pow_mul]; exact pow_le_pow_left₀ (by positivity) h2m _
    calc (2 * (m : Real) + 1) ^ (2 ^ (k + 4)) * (k : Real)
        ≤ u ^ ((e + 1) * 2 ^ (k + 4)) * u ^ k :=
          mul_le_mul hp hkk (Nat.cast_nonneg _) (by positivity)
      _ = u ^ ((e + 1) * 2 ^ (k + 4) + k) := (pow_add _ _ _).symm
  have htinv : (fejerLoss k a eta)⁻¹ ≤ u ^ (e * 2 ^ (k + 4)) := by
    unfold fejerLoss
    rw [← hmdef, inv_pow, inv_inv, pow_mul]
    exact pow_le_pow_left₀ hmpos.le hm1 _
  have htpos : 0 < fejerLoss k a eta := by unfold fejerLoss; positivity
  have hc0pos : 0 ≤ fejerDegenerateConst k a eta := by unfold fejerDegenerateConst; positivity
  have hfinal : 1 + k + (2 * e + 1) * 2 ^ (k + 4) ≤ fejerStepP k := by
    have : e = 7 * 4 ^ (k + 1) + 21 * k * 4 ^ (k + 1) + k + 52 := by rw [he, hA, hG]
    rw [this]; exact hexp
  have he_le : e ≤ fejerStepP k := by
    have h1 : 1 ≤ 2 ^ (k + 4) := Nat.one_le_two_pow
    have h2 : e ≤ (2 * e + 1) * 2 ^ (k + 4) := by nlinarith
    omega
  unfold fejerProductThreshold fejerExplicitThreshold
  rw [← ha, ← heta, ← hmdef]
  apply max_le
  · exact hm1.trans (pow_le_pow_right₀ hu1 he_le)
  · apply max_le
    · have h3 : (3 : Real) ≤ u ^ 2 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0:Real) ≤ 2) hu2 2]
      have he2 : 2 ≤ e := by rw [he]; omega
      exact h3.trans (pow_le_pow_right₀ hu1 (he2.trans he_le))
    · rw [one_mul, div_eq_mul_inv]
      calc 2 * fejerDegenerateConst k a eta * (fejerLoss k a eta)⁻¹
          ≤ u * u ^ ((e + 1) * 2 ^ (k + 4) + k) * u ^ (e * 2 ^ (k + 4)) :=
            mul_le_mul (mul_le_mul hu2 hc0 hc0pos hupos.le) htinv (inv_pos.mpr htpos).le
              (by positivity)
        _ = u ^ (1 + k + (2 * e + 1) * 2 ^ (k + 4)) := by
            rw [← pow_succ', ← pow_add]; congr 1; ring
        _ ≤ u ^ fejerStepP k := pow_le_pow_right₀ hu1 hfinal

/-- The tight radius at the Fejér density of dimension `k`: `0 < ζ′ ≤ 1` and
`ζ′⁻¹ ≤ exp(u^(fejerStepT k))`. -/
theorem tightZeta_fejer_inv_le_gen {gamma theta : Real} (k : Nat) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) :
    0 < tightZeta (fejerThetaOne theta gamma k / 4) ∧ tightZeta (fejerThetaOne theta gamma k / 4) ≤ 1 ∧
      (tightZeta (fejerThetaOne theta gamma k / 4))⁻¹ ≤
        Real.exp ((2 / (gamma * theta)) ^ fejerStepT k) := by
  obtain ⟨ha0, haS⟩ := fejerThetaOne_bounds k ht ht1 hg hg1
  obtain ⟨hz0, hzh⟩ := tightZeta_pos_le_half ha0 (by linarith)
  refine ⟨hz0, by linarith, ?_⟩
  have hs := fejer_tightRadiusExponent_le k ht ht1 hg hg1
  rw [mul_comm theta gamma] at hs
  set s := tightRadiusExponent (fejerThetaOne theta gamma k / 4) with hsdef
  have hs0 : 0 ≤ s := by
    rw [hsdef]; unfold tightRadiusExponent
    exact div_nonneg (by norm_num) (pow_nonneg ha0.le 11)
  have hinv : (tightZeta (fejerThetaOne theta gamma k / 4))⁻¹ = (2 : Real) ^ s := by
    unfold tightZeta; rw [← hsdef, Real.rpow_neg (by norm_num), inv_inv]
  rw [hinv]
  have h2e : (2 : Real) ^ s ≤ Real.exp s := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    apply Real.exp_le_exp.mpr
    have hl : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : Real) < 2 by norm_num); linarith
    nlinarith
  calc (2 : Real) ^ s ≤ Real.exp s := h2e
    _ ≤ Real.exp ((2 / (gamma * theta)) ^ fejerStepT k) := by
        apply Real.exp_le_exp.mpr
        unfold fejerStepT
        exact hs

end LeanProofs.GowersSzemeredi
