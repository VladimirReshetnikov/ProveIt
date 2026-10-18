import GowersSzemeredi.Proofs15FejerSelection

/-! Declarations of `Proofs15FejerSelection` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false
set_option maxRecDepth 10000

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

/-- **Lemma 15.5 with a single Fejér selection.** The statement of
Lemma 15.5 with `fejerSelectionExponent k` in place of
`arrangementSelectionExponent k`. -/
def FejerArrangementRestriction : Prop :=
  ∀ (k : Nat) (alpha beta eta : Real),
    1 ≤ k → 0 < alpha → 0 < beta → 0 < eta → eta ≤ 1 →
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N], N0 ≤ N → Nat.Prime N → Odd N →
      ∀ (B : Finset (Point N (k + 1)))
          (phi : Point N (k + 1) → ZMod N),
        (B.card : Real) = beta * (N : Real) ^ (k + 1) →
        alpha * beta ^ 15 * (N : Real) ^ (17 * k + 15) ≤
            respectedGeneralArrangementCount 8 B phi →
        ∃ B' : Finset (Point N (k + 1)), B' ⊆ B ∧
          (alpha * eta / 4) ^ fejerSelectionExponent k * beta ^ 15 *
              (N : Real) ^ (17 * k + 15) ≤
            generalArrangementCount 8 B' ∧
          (1 - eta) * generalArrangementCount 8 B' ≤
            respectedGeneralArrangementCount 8 B' phi

/-- The Fejér selection with an existential threshold. -/
theorem fejer_scale_estimate (k : Nat) (alpha scale eta : Real) (hk : 1 ≤ k)
    (halpha : 0 < alpha) (hscale : 0 < scale) (heta : 0 < eta) (heta_one : eta ≤ 1) :
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N], N0 ≤ N → Nat.Prime N → Odd N →
      ∀ (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N),
        (generalArrangementCount 8 B : Real) ≤ scale * (N : Real) ^ (17 * k + 15) →
        alpha * scale * (N : Real) ^ (17 * k + 15) ≤
            respectedGeneralArrangementCount 8 B phi →
        ∃ B' : Finset (Point N (k + 1)), B' ⊆ B ∧
          (alpha * eta / 4) ^ fejerSelectionExponent k * scale *
              (N : Real) ^ (17 * k + 15) ≤
            generalArrangementCount 8 B' ∧
          (1 - eta) * generalArrangementCount 8 B' ≤
            respectedGeneralArrangementCount 8 B' phi :=
  ⟨⌈fejerExplicitThreshold k alpha scale eta⌉₊, fun N _ hN =>
    fejer_scale_estimate_explicit k alpha scale eta hk halpha hscale heta heta_one N
      ((Nat.le_ceil _).trans (by exact_mod_cast hN))⟩

theorem fejer_arrangement_restriction : FejerArrangementRestriction := by
  intro k alpha beta eta hk halpha hbeta heta heta_one
  obtain ⟨N0, hN0⟩ := fejer_scale_estimate k alpha (beta ^ 15) eta hk halpha
    (pow_pos hbeta 15) heta heta_one
  exact ⟨N0, fun N _ hN hp ho B phi hBcard hl =>
    hN0 N hN hp ho B phi (selection_arrangement_real_upper beta B hBcard) hl⟩

/-- **The Fejér restriction implies the printed Lemma 15.5**, whose
exponent `2^(2^(k+4)+k+3)` is larger. -/
theorem lemma_15_5_of_fejer_restriction (h : FejerArrangementRestriction) : lemma_15_5 := by
  intro k alpha beta eta hk halpha hbeta heta heta_one
  obtain ⟨N0, hN0⟩ := h k alpha beta eta hk halpha hbeta heta heta_one
  refine ⟨N0, ?_⟩
  intro N _ hN hprime hodd B phi hBcard hrespected
  obtain ⟨B', hB'B, hlower, hdens⟩ := hN0 N hN hprime hodd B phi hBcard hrespected
  refine ⟨B', hB'B, le_trans ?_ hlower, hdens⟩
  have hG : 0 ≤ beta ^ 15 * (N : Real) ^ (17 * k + 15) := by positivity
  have hgeneral := selection_arrangement_real_upper beta B hBcard
  have hrespLe : (respectedGeneralArrangementCount 8 B phi : Real) ≤
      generalArrangementCount 8 B := by
    exact_mod_cast selection_respected_le_arrangement B phi
  rcases eq_or_lt_of_le hG with hG0 | hGpos
  · rw [mul_assoc, mul_assoc, ← hG0, mul_zero, mul_zero]
  have halpha1 : alpha ≤ 1 := by
    by_contra hlt
    push Not at hlt
    have : alpha * (beta ^ 15 * (N : Real) ^ (17 * k + 15)) ≤
        beta ^ 15 * (N : Real) ^ (17 * k + 15) := by
      calc alpha * (beta ^ 15 * (N : Real) ^ (17 * k + 15)) =
          alpha * beta ^ 15 * (N : Real) ^ (17 * k + 15) := by ring
        _ ≤ _ := hrespected
        _ ≤ _ := hrespLe
        _ ≤ _ := hgeneral
    linarith [mul_pos (sub_pos.mpr hlt) hGpos]
  have hbase0 : 0 ≤ alpha * eta / 4 := by positivity
  have hbase1 : alpha * eta / 4 ≤ 1 := by
    have h := mul_le_mul halpha1 heta_one heta.le zero_le_one
    linarith
  have hexp : fejerSelectionExponent k ≤ arrangementSelectionExponent k := by
    unfold fejerSelectionExponent arrangementSelectionExponent
    have h1 : k + 6 ≤ 2 ^ (2 ^ (k + 4) - 1) := by
      have h2 : k + 6 ≤ 2 ^ (k + 4) - 1 := by
        have := Nat.lt_two_pow_self (n := k)
        have e : 2 ^ (k + 4) = 16 * 2 ^ k := by rw [pow_add]; ring
        rw [e]
        omega
      exact h2.trans (Nat.lt_two_pow_self).le
    have h3 : 2 ^ (2 ^ (k + 4) + k + 3) = 2 ^ (k + 4) * 2 ^ (2 ^ (k + 4) - 1) := by
      rw [← pow_add]
      congr 1
      have := Nat.one_le_two_pow (n := k + 4)
      omega
    rw [h3]
    exact Nat.mul_le_mul_left _ h1
  have hpow := pow_le_pow_of_le_one hbase0 hbase1 hexp
  calc (alpha * eta / 4) ^ arrangementSelectionExponent k * beta ^ 15 *
        (N : Real) ^ (17 * k + 15)
      = (alpha * eta / 4) ^ arrangementSelectionExponent k *
          (beta ^ 15 * (N : Real) ^ (17 * k + 15)) := by ring
    _ ≤ (alpha * eta / 4) ^ fejerSelectionExponent k *
          (beta ^ 15 * (N : Real) ^ (17 * k + 15)) :=
        mul_le_mul_of_nonneg_right hpow hG
    _ = _ := by ring

end LeanProofs.GowersSzemeredi
