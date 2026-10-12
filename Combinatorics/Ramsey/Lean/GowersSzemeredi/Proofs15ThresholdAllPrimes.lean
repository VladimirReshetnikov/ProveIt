import GowersSzemeredi.Proofs15PrintedThreshold

/-! The displayed selection threshold already excludes characteristic two. -/

noncomputable section

namespace LeanProofs.GowersSzemeredi

/-- The density, respected-count and displayed threshold hypotheses force
the modulus to be at least three, without any primality assumption. -/
theorem selection_printed_threshold_three_le
    (k N : Nat) [NeZero N] (alpha beta eta : Real)
    (hk : 1 ≤ k) (halpha : 0 < alpha) (hbeta : 0 < beta)
    (heta : 0 < eta) (heta_one : eta ≤ 1)
    (hsize : (3 : Real) ^ (2 ^ (k + 4)) * k ≤
      (alpha * eta / 4) ^ arrangementSelectionExponent k * beta ^ 15 * N)
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (hcard : (B.card : Real) = beta * (N : Real) ^ (k + 1))
    (hrespected : alpha * beta ^ 15 * (N : Real) ^ (17 * k + 15) ≤
      respectedGeneralArrangementCount 8 B phi) : 3 ≤ N := by
  classical
  have hN : 0 < (N : Real) := by exact_mod_cast NeZero.pos N
  have hcardUpper : (B.card : Real) ≤ (N : Real) ^ (k + 1) := by
    have h := Finset.card_le_univ B
    simp only [Point, Fintype.card_fun, Fintype.card_fin, ZMod.card] at h
    exact_mod_cast h
  have hbeta_one : beta ≤ 1 := by
    rw [hcard] at hcardUpper
    exact (mul_le_mul_iff_of_pos_right (pow_pos hN _)).mp
      (by simpa using hcardUpper)
  have hcount : (respectedGeneralArrangementCount 8 B phi : Real) ≤
      generalArrangementCount 8 B := by
    unfold respectedGeneralArrangementCount generalArrangementCount countWhere
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro R hR
    simp only [Finset.mem_filter] at hR ⊢
    exact ⟨hR.1, hR.2.1⟩
  have hupper := selection_arrangement_real_upper beta B hcard
  have halpha_one : alpha ≤ 1 := by
    have h := hrespected.trans (hcount.trans hupper)
    apply (mul_le_mul_iff_of_pos_right
      (mul_pos (pow_pos hbeta 15) (pow_pos hN (17 * k + 15)))).mp
    simpa only [mul_assoc, one_mul] using h
  have ha : alpha * eta / 4 ≤ 1 := by
    have h := mul_le_one₀ halpha_one heta.le heta_one
    linarith
  have ht : (alpha * eta / 4) ^ arrangementSelectionExponent k ≤ 1 :=
    pow_le_one₀ (by positivity) ha
  have hb : beta ^ 15 ≤ 1 := pow_le_one₀ hbeta.le hbeta_one
  have hproduct : (alpha * eta / 4) ^ arrangementSelectionExponent k * beta ^ 15 ≤ 1 :=
    mul_le_one₀ ht (by positivity) hb
  have hlower : (3 : Real) ≤ (3 : Real) ^ (2 ^ (k + 4)) * k := by
    have hkR : (1 : Real) ≤ k := by exact_mod_cast hk
    calc
      3 = (3 : Real) ^ 1 := by norm_num
      _ ≤ (3 : Real) ^ (2 ^ (k + 4)) :=
        pow_le_pow_right₀ (by norm_num) (Nat.one_le_pow _ 2 (by norm_num))
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hkR
  have h := hlower.trans (hsize.trans
    (mul_le_of_le_one_left hN.le hproduct))
  exact_mod_cast h

/-- The annotated Lemma 15.5 threshold works over every prime: its other
hypotheses already rule out the only even prime. -/
theorem lemma_15_5_printed_threshold_all_primes
    (k N : Nat) [NeZero N] (alpha beta eta : Real)
    (hk : 1 ≤ k) (hprime : N.Prime)
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (heta : 0 < eta) (heta_one : eta ≤ 1)
    (hsize : (3 : Real) ^ (2 ^ (k + 4)) * k ≤
      (alpha * eta / 4) ^ arrangementSelectionExponent k * beta ^ 15 * N)
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (hcard : (B.card : Real) = beta * (N : Real) ^ (k + 1))
    (hrespected : alpha * beta ^ 15 * (N : Real) ^ (17 * k + 15) ≤
      respectedGeneralArrangementCount 8 B phi) :
    ∃ B' : Finset (Point N (k + 1)), B' ⊆ B ∧
      (alpha * eta / 4) ^ arrangementSelectionExponent k * beta ^ 15 *
        (N : Real) ^ (17 * k + 15) ≤ generalArrangementCount 8 B' ∧
      (1 - eta) * generalArrangementCount 8 B' ≤
        respectedGeneralArrangementCount 8 B' phi := by
  have hN3 := selection_printed_threshold_three_le k N alpha beta eta hk
    halpha hbeta heta heta_one hsize B phi hcard hrespected
  rcases hprime.eq_two_or_odd' with htwo | hodd
  · omega
  · exact lemma_15_5_printed_threshold k N alpha beta eta hk hprime hodd
      halpha hbeta heta heta_one hsize B phi hcard hrespected

end LeanProofs.GowersSzemeredi
