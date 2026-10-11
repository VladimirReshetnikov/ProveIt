import GowersSzemeredi.Proofs16PolyCoverThreeTheorem
import GowersSzemeredi.Proofs18LengthSixExplicit

/-! **Theorem 16.2 and Corollary 16.11 in dimension three, unconditionally.**

This module is a bridge. `theorem_16_2_three_of_profiles` (light,
kernel-checked locally) needs the recurrence profiles in dimensions one and
two at constants `K, p ≤ 2^2000`. These are the profiles that give Theorem 18.2
at length six (`Proofs18LengthSixExplicit`): `section16RecurrenceProfileWith_explicit`
at `k = 1, 2`, with constants bounded by `lengthSix_explicit_constants`.

Unlike the dimension-three statements of Notes Part J, nothing here assumes
Milićević's deep structure. The proof is Gowers's argument with polynomial
controls (Notes L.5): pieces of a uniform class, procedural stackability, and
the comparison with the printed controls.

The imports reach the port's Schmidt constants, so this module is checked on
the full-verification host. Every step is a definitional instantiation of a
kernel-checked statement. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- **Theorem 16.2 in dimension three.** -/
theorem theorem_16_2_three : Theorem162At 3 := by
  obtain ⟨hK1, hp1, hK2, hp2, hK1b, hp1b, hK2b, hp2b⟩ := lengthSix_explicit_constants
  -- unfold the named constants so that the profiles match syntactically
  have h1 : Section16RecurrenceProfileWith 1 (familyRecThr 1 explicitVarietyK ((1 + 1) * explicitVarietyP))
      (familyRecExp 1 ((1 + 1) * explicitVarietyP)) := by
    unfold explicitVarietyK explicitVarietyP; exact section16RecurrenceProfileWith_explicit 1
  have h2 : Section16RecurrenceProfileWith 2 (familyRecThr 2 explicitLiftK explicitLiftP)
      (familyRecExp 2 explicitLiftP) := by
    unfold explicitLiftK explicitLiftP; exact section16RecurrenceProfileWith_explicit 2
  exact theorem_16_2_three_of_profiles hK1 hp1 hK2 hp2 hK1b hp1b hK2b hp2b h1 h2

/-- **Corollary 16.11 in dimension three.** -/
theorem corollary_16_11_three : Corollary1611At 3 :=
  theorem_16_2_three.corollary_16_11 (by norm_num)

end LeanProofs.GowersSzemeredi
