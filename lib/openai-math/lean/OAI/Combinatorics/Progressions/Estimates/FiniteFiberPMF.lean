import OAI.Combinatorics.Progressions.Lattices.IntegerPMFNormalizedSource
import OAI.Combinatorics.Progressions.Probability.FiniteFiberLawSupport

namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped Classical

theorem toPMF_fiberLaw {X Y : Type*} [Fintype X] [Fintype Y]
    (p : FiniteProbabilityWeights X) (f : X → Y) :
    (p.fiberLaw f).toPMF = p.toPMF.map f := by
  ext y
  apply (ENNReal.toReal_eq_toReal_iff' ((p.fiberLaw f).toPMF.apply_ne_top y)
    ((p.toPMF.map f).apply_ne_top y)).mp
  rw [toPMF_toReal, toPMF_map_toReal]
  rfl

theorem toPMF_map_congr_on_support {X Y : Type*} [Fintype X]
    (p : FiniteProbabilityWeights X) (f g : X → Y)
    (h : ∀ x, p.weight x ≠ 0 → f x = g x) : p.toPMF.map f = p.toPMF.map g := by
  ext y
  apply (ENNReal.toReal_eq_toReal_iff' ((p.toPMF.map f).apply_ne_top y)
    ((p.toPMF.map g).apply_ne_top y)).mp
  rw [toPMF_map_toReal, toPMF_map_toReal]
  apply p.mean_congr_on_support
  intro x hx
  rw [h x hx]

end Erdos3.FiniteProbabilityWeights

end

end OAI
