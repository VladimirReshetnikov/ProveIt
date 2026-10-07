import OAI.Combinatorics.Progressions.Estimates.AllocatedEnormousProfiles
import OAI.Combinatorics.Progressions.Probability.IndependentEmbeddedMixture

namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

variable {J : Type*} [Fintype J] [DecidableEq J]
  {Ω R : J → Type*} [∀ j, Fintype (Ω j)] [∀ j, DecidableEq (Ω j)]
  [∀ j, Fintype (R j)] [∀ j, DecidableEq (R j)]

theorem pi_fiberLaw (p : ∀ j, FiniteProbabilityWeights (Ω j))
    (residue : ∀ j, Ω j → R j) :
    (pi p).fiberLaw (fun x j => residue j (x j)) =
      pi (fun j => (p j).fiberLaw (residue j)) := by
  apply ext_weight
  funext r
  rw [fiberLaw_weight_eq_mass, pi_fiber_mass]
  change (∏ j, (p j).mass _) = ∏ j, ((p j).fiberLaw (residue j)).weight (r j)
  simp only [fiberLaw_weight_eq_mass]

theorem pi_complexMean_disintegrate (p : ∀ j, FiniteProbabilityWeights (Ω j))
    (residue : ∀ j, Ω j → R j)
    (hp : ∀ j r, 0 < (p j).mass (Finset.univ.filter (fun x => residue j x = r)))
    (test : (∀ j, R j) → (∀ j, Ω j) → ℂ) :
    (pi p).complexMean (fun x => test (fun j => residue j (x j)) x) =
      (pi (fun j => (p j).fiberLaw (residue j))).complexMean (fun r =>
        (pi (fun j => (p j).condition
          (Finset.univ.filter (fun x => residue j x = r j)) (hp j (r j)))).complexMean
            (test r)) := by
  rw [(pi p).complexMean_disintegrate (fun x j => residue j (x j))
    (fun r => pi_fiber_mass_pos p residue r (fun j => hp j (r j))) test]
  rw [pi_fiberLaw]
  congr 1
  funext r
  rw [pi_condition_fiber]

end Erdos3.FiniteProbabilityWeights

end

end OAI
