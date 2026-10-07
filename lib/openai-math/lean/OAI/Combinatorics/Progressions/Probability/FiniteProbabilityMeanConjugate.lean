import OAI.Combinatorics.Progressions.Estimates.FiniteFiberTest

namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights
open scoped BigOperators

theorem complexMean_star {Ω : Type*} [Fintype Ω]
    (law : FiniteProbabilityWeights Ω) (f : Ω → ℂ) :
    law.complexMean (fun x => star (f x)) = star (law.complexMean f) := by
  simp only [complexMean, Complex.star_def, map_sum, map_mul, Complex.conj_ofReal]

end Erdos3.FiniteProbabilityWeights

end

end OAI
