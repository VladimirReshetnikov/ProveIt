import GowersSzemeredi.Proofs16PolyCoverThree
import GowersSzemeredi.Proofs16PolynomialLemma9WithRemainder

/-! **`PolyCoverAt 3`, unconditionally** (heavy bridge).

`polyCoverAt_three_of_family_lemma6` (light, kernel-checked locally) needs
the abstract family Lemma 16.6 in dimensions one and two at polynomial power
widths. `exists_abstract_family_lemma_16_6` supplies it in every dimension
from the polynomial recurrence. The import reaches the polynomial recurrence
profile, so this module is checked on the full-verification host. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- **The polynomial global-to-local cover in dimension three.** -/
theorem exists_polyCoverAt_three :
    ∃ C2 p2 K1 p1 : Nat, 2 ≤ C2 ∧ 0 < p2 ∧ 2 ≤ K1 ∧ 0 < p1 ∧
      PolyCoverAt 3 (polyThreeQb K1 p1)
        (polyThreeEb (familyWidthPrefactor C2) (familyWidthDivisor 2 p2) K1 p1) := by
  obtain ⟨C2, p2, hC2, hp2, h6⟩ := exists_abstract_family_lemma_16_6 2
  obtain ⟨K1, p1, hK1, hp1, h6'⟩ := exists_abstract_family_lemma_16_6 1
  exact ⟨C2, p2, K1, p1, hC2, hp2, hK1, hp1,
    polyCoverAt_three_of_family_lemma6 (familyWidthPrefactor_pos (by omega))
      (familyWidthDivisor_pos hp2) h6 (by omega) hp1 h6'⟩

end LeanProofs.GowersSzemeredi
