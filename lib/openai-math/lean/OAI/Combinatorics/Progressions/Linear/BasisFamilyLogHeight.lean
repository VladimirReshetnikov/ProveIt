import OAI.Combinatorics.Progressions.Estimates.RationalPowerHeight

namespace OAI

section

namespace Erdos3

def BasisFamilyLogHeight {ι κ V : Type*} [AddCommGroup V] [Module ℚ V]
    (b : Module.Basis ι ℚ V) (v : κ → V) (p : ℝ) : Prop :=
  ∀ i j, rationalLogHeight (b.repr (v i) j) ≤ p

end Erdos3

end

end OAI
