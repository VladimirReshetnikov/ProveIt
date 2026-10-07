import GowersSzemeredi.Proofs18FiveTermIterationEnvelope
import GowersSzemeredi.Proofs18QuadraticSourceThreshold

/-! An explicit improved five-term bound and the source's exact five-term instance.
These restricted instances do not assert the all-length theorem. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

set_option exponentiation.threshold 2048 in
/-- The complete five-term threshold is bounded by an explicit base-two tower. -/
theorem fejerFiveTermThreshold_le_explicit_tower {delta : Real}
    (hδ : 0 < delta) (hδhalf : delta ≤ 1 / 2) :
    fejerFiveTermThreshold delta ≤ (2 : Real) ^ ((2 : Real) ^ (delta⁻¹ ^ ((2 : Nat) ^ 76))) := by
  let u : Real := delta⁻¹
  let q : Nat := 2 ^ 74
  let E : Nat := 2 ^ 76
  have hu : 2 ≤ u := by
    change 2 ≤ delta⁻¹
    rw [← one_div]
    apply (le_div_iff₀ hδ).mpr
    linarith only [hδhalf]
  have hu0 : 0 ≤ u := by linarith only [hu]
  have hu1 : 1 ≤ u := by linarith only [hu]
  have hb : 2 / delta ≤ u ^ (2 : Nat) := by
    rw [div_eq_mul_inv]
    change 2 * u ≤ u ^ 2
    nlinarith only [hu]
  have habsorb : (2 / delta) ^ ((2 : Nat) ^ 73) ≤ u ^ q := by
    have h := pow_le_pow_left₀ (by positivity : (0 : Real) ≤ 2 / delta) hb ((2 : Nat) ^ 73)
    rw [← pow_mul, show (2 : Nat) * 2 ^ 73 = 2 ^ 74 by norm_num] at h
    exact h
  have hqE : q + 2 ≤ E := by norm_num [q, E]
  have hx1 : 1 ≤ u ^ q := one_le_pow₀ hu1
  have hinner : 1 + 2 * u ^ q ≤ u ^ E := by
    calc
      _ ≤ u ^ q * 4 := by linarith only [hx1]
      _ ≤ u ^ q * u ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith only [hu] : (4 : Real) ≤ u ^ 2) (by positivity)
      _ = u ^ (q + 2) := (pow_add u q 2).symm
      _ ≤ _ := pow_le_pow_right₀ hu1 hqE
  have hexp : Real.exp (Real.exp (u ^ q)) ≤ (2 : Real) ^ ((2 : Real) ^ (u ^ E)) := by
    apply (section18_exp_le_two_rpow (Real.exp_pos _).le).trans
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    calc
      2 * Real.exp (u ^ q) ≤ 2 * (2 : Real) ^ (2 * u ^ q) :=
        mul_le_mul_of_nonneg_left (section18_exp_le_two_rpow (by positivity)) (by norm_num)
      _ = (2 : Real) ^ (1 + 2 * u ^ q) := by
        rw [Real.rpow_add (by norm_num : (0 : Real) < 2), Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hinner
  apply (fejerFiveTermThreshold_le_double_exp hδ (by linarith only [hδhalf])).trans
  exact (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr habsorb)).trans hexp

/-- The simplified five-term bound is smaller than the paper's exact
five-term instance, whose innermost power is 2^16384. -/
theorem fejerFiveTermThreshold_le_source {delta : Real}
    (hδ : 0 < delta) (hδhalf : delta ≤ 1 / 2) :
    fejerFiveTermThreshold delta ≤ szemerediThreshold delta 5 := by
  apply (fejerFiveTermThreshold_le_explicit_tower hδ hδhalf).trans
  have hu : 1 ≤ delta⁻¹ := (one_le_inv₀ hδ).mpr (by linarith)
  have hsource : (2 : Real) ^ ((2 : Real) ^ (delta⁻¹ ^ ((2 : Nat) ^ 16384))) =
      szemerediThreshold delta 5 := by
    unfold szemerediThreshold
    rw [show (2 : Real) ^ (5 + 9 : Nat) = 16384 by norm_num]
    simp only [← Real.rpow_natCast, Nat.cast_pow, Nat.cast_ofNat]
  rw [← hsource]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  exact pow_le_pow_right₀ hu (Nat.pow_le_pow_right (by norm_num) (by norm_num : 76 ≤ 16384))

/-- The new five-term threshold is strictly smaller than the source's
five-term threshold over the entire stated density range. -/
theorem five_term_explicit_tower_lt_source {delta : Real}
    (hδ : 0 < delta) (hδhalf : delta ≤ 1 / 2) :
    (2 : Real) ^ ((2 : Real) ^ (delta⁻¹ ^ ((2 : Nat) ^ 76))) <
      szemerediThreshold delta 5 := by
  have hu : 1 < delta⁻¹ := by
    have hh : 2 ≤ delta⁻¹ := by
      rw [← one_div]
      apply (le_div_iff₀ hδ).mpr
      linarith
    linarith
  have hsource : (2 : Real) ^ ((2 : Real) ^ (delta⁻¹ ^ ((2 : Nat) ^ 16384))) =
      szemerediThreshold delta 5 := by
    unfold szemerediThreshold
    rw [show (2 : Real) ^ (5 + 9 : Nat) = 16384 by norm_num]
    simp only [← Real.rpow_natCast, Nat.cast_pow, Nat.cast_ofNat]
  rw [← hsource]
  apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
  apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
  exact pow_lt_pow_right₀ hu (Nat.pow_lt_pow_right (by norm_num) (by norm_num : 76 < 16384))

/-- A strictly smaller numerical threshold guarantees a five-term progression. -/
theorem natural_five_term_explicit_tower
    (delta : Real) (N : Nat) (hδ : 0 < delta) (hδhalf : delta ≤ 1 / 2)
    (hN : (2 : Real) ^ ((2 : Real) ^ (delta⁻¹ ^ ((2 : Nat) ^ 76))) ≤ N)
    (A : Finset Nat) (hA : A ⊆ Finset.Icc 1 N) (hcard : delta * N ≤ A.card) : HasNatAP A 5 :=
  natural_five_term_fejer delta hδ (by linarith only [hδhalf]) N
    ((fejerFiveTermThreshold_le_explicit_tower hδ hδhalf).trans hN) A hA hcard

/-- The source's exact five-term instance of Theorem 18.2. -/
theorem theorem_18_2_five_holds
    (delta : Real) (N : Nat) (hδ : 0 < delta) (hδhalf : delta ≤ 1 / 2)
    (hN : szemerediThreshold delta 5 ≤ N)
    (A : Finset Nat) (hA : A ⊆ Finset.Icc 1 N) (hcard : delta * N ≤ A.card) : HasNatAP A 5 :=
  natural_five_term_fejer delta hδ (by linarith only [hδhalf]) N
    ((fejerFiveTermThreshold_le_source hδ hδhalf).trans hN) A hA hcard

end LeanProofs.GowersSzemeredi
