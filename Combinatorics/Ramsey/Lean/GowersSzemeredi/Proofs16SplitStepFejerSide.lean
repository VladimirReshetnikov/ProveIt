import GowersSzemeredi.Proofs16SplitStepFejer
import GowersSzemeredi.Proofs16UniformCoverTwoFejerSide

/-! Declarations of `Proofs16SplitStepFejer` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

section
open BaseCase

/-- **A split uniform class in every dimension `k ≥ 2` under the Fejér θ₁
and the tight radius**, with degrees `splitPairWith (2^46) (2^46) k`, so
`log₂ D_k ≤ 22·2^k` (`split_pair_fejer_bound`). -/
theorem splitUniformClass_all_fejer (Kc pc : Nat → Nat) (hK : ∀ k, 1 ≤ Kc k) (hp : ∀ k, 0 < pc k)
    (hlem : ∀ k, 1 ≤ k → AbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor (Kc k)) (familyWidthDivisor k (pc k)))) :
    ∀ k, 2 ≤ k →
      Nonempty (SplitUniformClass k (classV Kc pc k) (splitPairWith splitSeedFejer splitSeedFejer k).1
        (splitPairWith splitSeedFejer splitSeedFejer k).2) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    have hV1 := one_le_classV Kc pc 2
    have hc1 := const_le_classV_succ Kc pc 1
    rw [splitPairWith_two]
    exact splitUniformClass_two_fejer (hK 1) (hp 1) (hlem 1 le_rfl) hV1 (hc1.1.trans le_rfl)
      (hc1.2.trans le_rfl) (by unfold splitSeedFejer; exact le_rfl)
  | succ k hk ih =>
    obtain ⟨C⟩ := ih
    obtain ⟨ha, hD⟩ := split_pair_fejer_basic k hk
    have hV1 := one_le_classV Kc pc k
    have hc := const_le_classV_succ Kc pc k
    rw [splitPairWith_succ _ _ hk, ← splitStepDFejer_eq]
    exact splitUniformClass_succ_fejer (by omega) hV1 ha hD C (hK k) (hp k) (hlem k (by omega))
      (classV_le_succ Kc pc k) hc.1 hc.2

end

end LeanProofs.GowersSzemeredi
