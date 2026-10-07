import OAI.Combinatorics.Progressions.Dynamics.CanonicalZeroLayerBudgetedInitialization

namespace OAI

section

namespace Erdos3

theorem unconditionedCommonSideScalarRatio_two_le {n : ℕ} (hn : 1 ≤ n) :
    2 ≤ unconditionedCommonSideScalarRatio n := by
  have hmul := Nat.mul_le_mul hn (unconditionedScalarPrimeRatio_two_le n)
  unfold unconditionedCommonSideScalarRatio
  omega

end Erdos3

end

end OAI
