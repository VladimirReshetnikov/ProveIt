import GowersSzemeredi.Proofs16DenseBihomPiece
import GowersSzemeredi.Proofs16SharperLineExtractor

/-! Polynomial bounds for the variety route's family size.

The extraction count and density of the variety route
(`section16VarietyExtractionCount`, `section16VarietyExtractionDensity`) are
built from `bihomFamilySize (densePieceMassGen section16SharperLineMass) γ θ`.
Its size enters the logarithmic losses of the budget comparison
(`Proofs16VarietyPieceBudget`). This module bounds it by a power of
`x = 2/(θγ)`:
* `sharperLineMass_ge`: `κ'(γ,β) ≥ t^11194·β^1165` for `t ≤ min(γ, 1/2)`;
* `densePieceMassGen_sharper_ge`: the piece mass is `≥ t^14424120`,
  `t = θγ/2`;
* `bihomFamilySize_sharper_le_pow`: the family size is `≤ x^(2^24)`.

The exponents are treated as opaque natural numbers, so no tactic evaluates a
large numeral power. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The sharper line mass is at least `t^11194·β^1165` for `t ≤ γ` and `t ≤ 1/2`. -/
theorem sharperLineMass_ge {gamma beta t : Real} (ht : 0 < t) (htg : t ≤ gamma)
    (ht2 : t ≤ 1 / 2) (hb : 0 ≤ beta) :
    t ^ 11194 * beta ^ 1165 ≤ section16SharperLineMass gamma beta := by
  unfold section16SharperLineMass
  have h2 : (2 : Real) ^ (-(1882 : Real)) = (1 / 2) ^ (1882 : Nat) := by
    rw [Real.rpow_neg (by norm_num), show (1882 : Real) = ((1882 : Nat) : Real) by norm_num,
      Real.rpow_natCast, one_div, inv_pow]
  rw [h2]
  have hA : t ^ 1882 ≤ (1 / 2 : Real) ^ 1882 := pow_le_pow_left₀ ht.le ht2 _
  have hB : t ^ 9312 ≤ gamma ^ 9312 := pow_le_pow_left₀ ht.le htg _
  have hsplit : t ^ 11194 = t ^ 1882 * t ^ 9312 := by rw [← pow_add]
  rw [hsplit]
  have hb' : 0 ≤ beta ^ 1165 := pow_nonneg hb _
  calc t ^ 1882 * t ^ 9312 * beta ^ 1165 ≤ (1 / 2) ^ 1882 * gamma ^ 9312 * beta ^ 1165 := by
        apply mul_le_mul_of_nonneg_right _ hb'
        exact mul_le_mul hA hB (by positivity) (by positivity)
    _ = _ := rfl

/-- **The dense piece mass is at least `(θγ/2)^14424120`.** -/
theorem densePieceMassGen_sharper_ge {theta gamma : Real} (ht : 0 < theta) (ht1 : theta ≤ 1)
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    (theta * gamma / 2) ^ 14424120 ≤ densePieceMassGen section16SharperLineMass gamma theta := by
  unfold densePieceMassGen
  obtain ⟨t, htdef⟩ : ∃ t, theta * gamma / 2 = t := ⟨_, rfl⟩
  have ht0 : 0 < t := by rw [← htdef]; positivity
  have htg : t ≤ gamma := by rw [← htdef]; nlinarith
  have ht2 : t ≤ 1 / 2 := by rw [← htdef]; nlinarith [mul_le_one₀ ht1 hg.le hg1]
  have htt : t ≤ theta / 2 := by rw [← htdef]; nlinarith
  have hsq : t ^ 2 ≤ theta / 2 / 2 := by nlinarith
  rw [htdef]
  -- the inner line mass
  have hk1 : t ^ 12359 ≤ section16SharperLineMass gamma (theta / 2) := by
    have h := sharperLineMass_ge ht0 htg ht2 (by positivity : (0 : Real) ≤ theta / 2)
    have h' : t ^ 1165 ≤ (theta / 2) ^ 1165 := pow_le_pow_left₀ ht0.le htt _
    calc t ^ 12359 = t ^ 11194 * t ^ 1165 := by rw [← pow_add]
      _ ≤ t ^ 11194 * (theta / 2) ^ 1165 := mul_le_mul_of_nonneg_left h' (by positivity)
      _ ≤ _ := h
  obtain ⟨k1, hk1def⟩ : ∃ k, section16SharperLineMass gamma (theta / 2) = k := ⟨_, rfl⟩
  rw [hk1def] at hk1 ⊢
  -- the second argument
  have hb2 : t ^ 12361 ≤ k1 * theta / 2 / 2 := by
    have : k1 * theta / 2 / 2 = k1 * (theta / 2 / 2) := by ring
    rw [this]
    calc t ^ 12361 = t ^ 12359 * t ^ 2 := by rw [← pow_add]
      _ ≤ k1 * (theta / 2 / 2) :=
          mul_le_mul hk1 hsq (by positivity) ((pow_nonneg ht0.le _).trans hk1)
  obtain ⟨b2, hb2def⟩ : ∃ b, k1 * theta / 2 / 2 = b := ⟨_, rfl⟩
  rw [hb2def] at hb2 ⊢
  have hb20 : 0 ≤ b2 := (pow_nonneg ht0.le _).trans hb2
  have hk2 : t ^ 11194 * b2 ^ 1165 ≤ section16SharperLineMass gamma b2 :=
    sharperLineMass_ge ht0 htg ht2 hb20
  have hpow : (t ^ 12361) ^ 1165 ≤ b2 ^ 1165 := pow_le_pow_left₀ (pow_nonneg ht0.le _) hb2 _
  calc t ^ 14424120 = t ^ 11194 * (t ^ 12361) ^ 1165 * t ^ 12361 := by
        rw [show (14424120 : Nat) = 11194 + 12361 * 1165 + 12361 by norm_num, pow_add, pow_add,
          pow_mul]
    _ ≤ t ^ 11194 * b2 ^ 1165 * b2 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hpow (pow_nonneg ht0.le _)) hb2
          (pow_nonneg ht0.le _) (mul_nonneg (pow_nonneg ht0.le _) (pow_nonneg hb20 _))
    _ ≤ section16SharperLineMass gamma b2 * b2 := mul_le_mul_of_nonneg_right hk2 hb20

/-- **The family size is at most `(2/(θγ))^(2^24)`.** -/
theorem bihomFamilySize_sharper_le_pow {theta gamma : Real} (ht : 0 < theta) (ht1 : theta ≤ 1)
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    (bihomFamilySize (densePieceMassGen section16SharperLineMass) gamma theta : Real) ≤
      (2 / (theta * gamma)) ^ ((2 : Nat) ^ 24) := by
  have hmass := densePieceMassGen_sharper_ge ht ht1 hg hg1
  unfold bihomFamilySize
  obtain ⟨m, hmdef⟩ : ∃ m, densePieceMassGen section16SharperLineMass gamma theta = m := ⟨_, rfl⟩
  rw [hmdef] at hmass ⊢
  obtain ⟨x, hxdef⟩ : ∃ x, 2 / (theta * gamma) = x := ⟨_, rfl⟩
  rw [hxdef]
  have htx : theta * gamma / 2 = x⁻¹ := by rw [← hxdef, inv_div]
  rw [htx] at hmass
  -- `hmass` carries a numeral power; it is cleared before any arithmetic tactic.
  have hx2 : 2 ≤ x := by
    clear hmass
    rw [← hxdef, le_div_iff₀ (by positivity)]
    nlinarith [mul_le_one₀ ht1 hg.le hg1]
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hm0 : 0 < m := (pow_pos (inv_pos.mpr hx0) _).trans_le hmass
  -- `γ⁻² ≤ x²`
  have hginv : gamma⁻¹ ≤ x := by
    clear hmass
    rw [← hxdef, inv_eq_one_div, div_le_div_iff₀ hg (by positivity)]
    nlinarith
  have hg2 : gamma ^ (-(2 : Int)) ≤ x ^ 2 := by
    rw [zpow_neg, zpow_ofNat, ← inv_pow]
    exact pow_le_pow_left₀ (by positivity) hginv 2
  -- `m⁻¹ ≤ x^14424120`
  have hminv : m⁻¹ ≤ x ^ 14424120 := by
    have := inv_anti₀ (pow_pos (inv_pos.mpr hx0) _) hmass
    rwa [inv_pow, inv_inv] at this
  clear hmass
  obtain ⟨E, hE⟩ : ∃ E : Nat, 14424120 = E := ⟨_, rfl⟩
  have hEbig : E + 4 ≤ (2 : Nat) ^ 24 := by rw [← hE]; norm_num
  rw [hE] at hminv
  clear hE
  have hceil : ((⌈gamma ^ (-(2 : Int)) / m⌉₊ + 1 : Nat) : Real) ≤ x ^ 2 * x ^ E + 2 := by
    push_cast
    have hc := Nat.ceil_lt_add_one (show 0 ≤ gamma ^ (-(2 : Int)) / m by positivity)
    have hdiv : gamma ^ (-(2 : Int)) / m ≤ x ^ 2 * x ^ E := by
      rw [div_eq_mul_inv]
      exact mul_le_mul hg2 hminv (by positivity) (by positivity)
    linarith
  have hxE : (1 : Real) ≤ x ^ E := one_le_pow₀ hx1
  have h4 : (4 : Real) ≤ x ^ 2 := by nlinarith
  calc ((⌈gamma ^ (-(2 : Int)) / m⌉₊ + 1 : Nat) : Real) ≤ x ^ 2 * x ^ E + 2 := hceil
    _ ≤ x ^ 2 * x ^ E + x ^ 2 * x ^ E := by nlinarith
    _ ≤ x ^ 2 * (x ^ 2 * x ^ E) := by nlinarith
    _ = x ^ (E + 4) := by ring
    _ ≤ x ^ ((2 : Nat) ^ 24) := pow_le_pow_right₀ hx1 hEbig

/-- **Counts of the form `⌈fam·e^mb⌉ + 1` cost `log(fam+3) + mb`.** -/
theorem log_extraction_count_le {fam mb : Real} (hf : 0 ≤ fam) (hm : 0 ≤ mb) :
    Real.log ((((Nat.ceil (fam * Real.exp mb) + 1 : Nat)) : Real) + 1) ≤
      Real.log (fam + 3) + mb := by
  have he : 1 ≤ Real.exp mb := Real.one_le_exp hm
  have hc := Nat.ceil_lt_add_one (mul_nonneg hf (Real.exp_pos mb).le)
  have hle : (((Nat.ceil (fam * Real.exp mb) + 1 : Nat)) : Real) + 1 ≤ (fam + 3) * Real.exp mb := by
    push_cast
    nlinarith
  have hpos : 0 < (((Nat.ceil (fam * Real.exp mb) + 1 : Nat)) : Real) + 1 := by positivity
  calc Real.log ((((Nat.ceil (fam * Real.exp mb) + 1 : Nat)) : Real) + 1)
      ≤ Real.log ((fam + 3) * Real.exp mb) := Real.log_le_log hpos hle
    _ = Real.log (fam + 3) + mb := by
        rw [Real.log_mul (by linarith) (Real.exp_pos mb).ne', Real.log_exp]

/-- **Milićević's bound is at most `(4/c)^D`.** -/
theorem milicevicBound_le {D : Nat} {c : Real} (hc : 0 < c) (hc1 : c ≤ 1) :
    milicevicBound D c ≤ (4 / c) ^ D := by
  unfold milicevicBound
  have hlog : Real.log c⁻¹ ≤ c⁻¹ := (Real.log_le_sub_one_of_pos (inv_pos.mpr hc)).trans (by linarith)
  have hci : 1 ≤ c⁻¹ := (one_le_inv₀ hc).mpr hc1
  have hbase : 2 + 2 * Real.log c⁻¹ ≤ 4 / c := by
    rw [div_eq_mul_inv]; linarith
  exact pow_le_pow_left₀ (two_le_milicevic_base hc hc1 |>.trans' (by norm_num)) hbase D

end LeanProofs.GowersSzemeredi
