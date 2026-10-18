import GowersSzemeredi.Proofs18RothThresholdBounds
import GowersSzemeredi.Proofs02Roth
import GowersSzemeredi.Proofs18SingleLengthStatements
import GowersSzemeredi.Proofs18FiveTermSourceThreshold
import GowersSzemeredi.Proofs18QuadraticSourceThresholdSide

/-! Theorem 18.2 and Corollary 18.7 at every length up to five.

The catalogue entries `theorem_18_2` and `corollary_18_7` quantify over all
lengths `k`. This module names the statements at one length
(`Theorem182At`, `Corollary187At`), records that the catalogue entries are
exactly the conjunctions over all positive lengths, and proves every length
`k ≤ 5` with the source's exact displayed thresholds:

* `k ≤ 3`: from Roth's theorem with its explicit constant
  (`roth_explicit_threshold`). For `delta ≤ 1/2` and every `k`,
  `exp(exp(10^12/delta)) ≤ szemerediThreshold delta k`, because with
  `u = 1/delta ≥ 2` one has `10^12*u ≤ u^41` and two spare powers
  absorb the conversion to base two. A three-term progression contains
  the shorter ones.
* `k = 4, 5`: the existing `theorem_18_2_four_holds` and
  `theorem_18_2_five_holds`.

Corollary 18.7 at each such length follows from Theorem 18.2 at density one
half (`corollary_18_7_at_of_half_density`). -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Roth's explicit threshold lies below the source threshold at every length. -/
theorem roth_threshold_le_szemerediThreshold (k : Nat) {delta : Real}
    (hδ : 0 < delta) (hδ2 : delta ≤ 1 / 2) :
    Real.exp (Real.exp (1000000000000 * delta⁻¹)) ≤ szemerediThreshold delta k := by
  unfold szemerediThreshold
  apply roth_exp_exp_le_two_tower (n := k + 9) ?_ (by omega)
  rw [← one_div, le_div_iff₀ hδ]
  linarith only [hδ2]

/-- **Theorem 18.2 for lengths at most three**, from Roth's theorem. -/
theorem theorem_18_2_le_three {k : Nat} (hk : k ≤ 3) : Theorem182At k := by
  intro delta N hδ hδ2 hN A hA hc
  obtain ⟨a, d, hd, h⟩ := roth_explicit_threshold delta N hδ
    ((roth_threshold_le_szemerediThreshold k hδ hδ2).trans hN) A hA hc
  exact ⟨a, d, hd, fun i hi => h i (by omega)⟩

/-- **Theorem 18.2 at every length up to five**, with the source thresholds. -/
theorem theorem_18_2_le_five {k : Nat} (hk : k ≤ 5) : Theorem182At k := by
  rcases (by omega : k ≤ 3 ∨ k = 4 ∨ k = 5) with h | rfl | rfl
  · exact theorem_18_2_le_three h
  · exact fun delta N hδ hδ2 hN A hA hc => theorem_18_2_four_holds delta N hδ hδ2 hN A hA hc
  · exact fun delta N hδ hδ2 hN A hA hc => theorem_18_2_five_holds delta N hδ hδ2 hN A hA hc

/-- **Corollary 18.7 at every length up to five.** -/
theorem corollary_18_7_le_five {k : Nat} (hk : k ≤ 5) : Corollary187At k :=
  (theorem_18_2_le_five hk).corollary_18_7

end LeanProofs.GowersSzemeredi
