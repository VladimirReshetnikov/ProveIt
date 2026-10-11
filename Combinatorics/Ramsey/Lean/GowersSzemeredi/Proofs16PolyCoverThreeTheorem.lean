import GowersSzemeredi.Proofs16PolyCoverThreeBounds
import GowersSzemeredi.Proofs16AbstractFamily
import GowersSzemeredi.Proofs16CorollaryLowDimensions

/-! Theorem 16.2 in dimension three by route (II) (Notes L.5).

The recurrence profiles in dimensions one and two give the abstract family
Lemma 16.6 there (`abstractFamilyLemma166At_of`), hence `PolyCoverAt 3`
(`polyCoverAt_three_of_family_lemma6`). With `W₀ = K₁ + p₁ + K₂ + p₂` its
count is at most `W^(2^321)` and its width exponent at least `W^(-2^361)`,
where `W = W₀·2/(γθρ)` (`Proofs16PolyCoverThreeBounds`). Both lie inside the
printed controls (`theorem162At_of_polyCover` with `D = 2^361 ≤ 2^(2^11)`).

The profile constants are only required to be at most `2^2000`, as at length
six; the explicit constants satisfy this (`lengthSix_explicit_constants`). -/
set_option autoImplicit false
set_option exponentiation.threshold 1024
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- **Theorem 16.2 in dimension three from the profiles in dimensions one and two.** -/
theorem theorem_16_2_three_of_profiles {K1 p1 K2 p2 : Nat} (hK1 : 2 ≤ K1) (hp1 : 0 < p1)
    (hK2 : 2 ≤ K2) (hp2 : 0 < p2)
    (hK1b : (K1 : Real) ≤ 2 ^ 2000) (hp1b : (p1 : Real) ≤ 2 ^ 2000)
    (hK2b : (K2 : Real) ≤ 2 ^ 2000) (hp2b : (p2 : Real) ≤ 2 ^ 2000)
    (hrec1 : Section16RecurrenceProfileWith 1 (familyRecThr 1 K1 p1) (familyRecExp 1 p1))
    (hrec2 : Section16RecurrenceProfileWith 2 (familyRecThr 2 K2 p2) (familyRecExp 2 p2)) :
    Theorem162At 3 := by
  have hcov := polyCoverAt_three_of_family_lemma6
    (familyWidthPrefactor_pos (show 1 ≤ K2 by omega)) (familyWidthDivisor_pos hp2)
    (abstractFamilyLemma166At_of 2 hK2 hp2 hrec2) (show 0 < K1 by omega) hp1
    (abstractFamilyLemma166At_of 1 hK1 hp1 hrec1)
  set W0 : Real := (K1 : Real) + p1 + K2 + p2 with hW0def
  have hK1' : (2 : Real) ≤ K1 := by exact_mod_cast hK1
  have hK2' : (2 : Real) ≤ K2 := by exact_mod_cast hK2
  have hp10 : (0 : Real) ≤ p1 := Nat.cast_nonneg _
  have hp20 : (0 : Real) ≤ p2 := Nat.cast_nonneg _
  have hW0 : 1 ≤ W0 := by linarith only [hK1', hK2', hp10, hp20, hW0def]
  have hW0' : W0 ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (3 + 6)) - 1) := by
    have h4 : W0 ≤ 2 ^ 2002 := by
      have : (2 : Real) ^ 2002 = 4 * 2 ^ 2000 := by
        rw [show (2002 : Nat) = 2 + 2000 from rfl, pow_add]; norm_num
      rw [this]; linarith only [hK1b, hp1b, hK2b, hp2b, hW0def]
    have hn : 2002 ≤ (2 : Nat) ^ ((2 : Nat) ^ (3 + 6)) - 1 := by
      refine Nat.le_sub_one_of_lt (lt_of_lt_of_le (by norm_num : 2002 < (2 : Nat) ^ 11) ?_)
      exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
    exact h4.trans (pow_le_pow_right₀ (by norm_num) hn)
  refine theorem162At_of_polyCover hcov hW0 hW0' (D := (2 : Nat) ^ 361)
    (Nat.pow_le_pow_right (by norm_num) (by norm_num)) ?_ ?_
  · intro gamma theta rho hg hg1 ht ht1 hr hr1
    obtain ⟨hB2, -, -, -⟩ := three_base_facts hg hg1 ht ht1 hr hr1 hW0
    exact le_pow_mono hB2 (Nat.pow_le_pow_right (by norm_num) (by norm_num))
      (polyThreeQb_le_power hg hg1 ht ht1 hr hr1 hW0
        (by linarith only [hp10, hK2', hp20, hW0def]) (by linarith only [hK1', hK2', hp20, hW0def]))
  · intro gamma theta rho hg hg1 ht ht1 hr hr1
    have h := (polyThreeEb_inv_le_power (show 0 < K1 by omega) hp1 (show 1 ≤ K2 by omega) hp2
      hg hg1 ht ht1 hr hr1 hW0 (by linarith only [hp10, hK2', hp20, hW0def])
      (by linarith only [hK1', hK2', hp20, hW0def]) (by linarith only [hK1', hp10, hp20, hW0def])
      (by linarith only [hK1', hp10, hK2', hW0def]))
    have := inv_anti₀ (inv_pos.mpr h.1) h.2
    rwa [inv_inv] at this

/-- **Corollary 16.11 in dimension three from the profiles in dimensions one and two.** -/
theorem corollary_16_11_three_of_profiles {K1 p1 K2 p2 : Nat} (hK1 : 2 ≤ K1) (hp1 : 0 < p1)
    (hK2 : 2 ≤ K2) (hp2 : 0 < p2)
    (hK1b : (K1 : Real) ≤ 2 ^ 2000) (hp1b : (p1 : Real) ≤ 2 ^ 2000)
    (hK2b : (K2 : Real) ≤ 2 ^ 2000) (hp2b : (p2 : Real) ≤ 2 ^ 2000)
    (hrec1 : Section16RecurrenceProfileWith 1 (familyRecThr 1 K1 p1) (familyRecExp 1 p1))
    (hrec2 : Section16RecurrenceProfileWith 2 (familyRecThr 2 K2 p2) (familyRecExp 2 p2)) :
    Corollary1611At 3 :=
  (theorem_16_2_three_of_profiles hK1 hp1 hK2 hp2 hK1b hp1b hK2b hp2b hrec1 hrec2).corollary_16_11
    (by norm_num)

end LeanProofs.GowersSzemeredi
