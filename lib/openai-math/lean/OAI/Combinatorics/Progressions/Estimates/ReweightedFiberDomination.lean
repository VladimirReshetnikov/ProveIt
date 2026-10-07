import OAI.Combinatorics.Progressions.Probability.FiniteExcessMassCap
import OAI.Combinatorics.Progressions.Probability.IntervalDivisorProbability

namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped Classical

theorem fiberLaw_mass_indicator {X Y : Type*} [Fintype X] [Fintype Y]
    (p : FiniteProbabilityWeights X) (F : X → Y) (G : Finset Y) :
    (p.fiberLaw F).mass G = p.mean (fun x => if F x ∈ G then 1 else 0) := by
  rw [p.fiberLaw_mass_preimage, ← p.mean_indicator]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem reweightPositive_fiber_mass_le {X Y : Type*} [Fintype X] [Fintype Y]
    (p : FiniteProbabilityWeights X) (F : X → Y) (D g : X → ℝ)
    (hD0 : ∀ x, 0 ≤ D x) (hD : 0 < p.mean D) {C ε a : ℝ}
    (ha : 0 < a) (hlower : a ≤ p.mean D) (hg : ∀ x, g x ≤ C)
    (G : Finset Y)
    (he : |p.mean (fun x => D x * (if F x ∈ G then 1 else 0)) -
      p.mean (fun x => g x * (if F x ∈ G then 1 else 0))| ≤ ε) :
    ((p.reweightPositive D hD0 hD).fiberLaw F).mass G ≤
      (C / a) * (p.fiberLaw F).mass G + ε / a := by
  rw [fiberLaw_mass_indicator, fiberLaw_mass_indicator]
  have hφ (x : X) : 0 ≤ (if F x ∈ G then 1 else 0 : ℝ) := by split_ifs <;> norm_num
  have hb := p.mean_mul_le_of_capped_comparison D g (fun x => if F x ∈ G then 1 else 0) hφ hg he
  have hn := p.reweightPositive_test_le D hD0 hD (fun x => if F x ∈ G then 1 else 0) hφ ha hlower hb
  convert hn using 1; ring

theorem reweightPositive_fiber_excess_le {X Y : Type*} [Fintype X] [Fintype Y]
    (p : FiniteProbabilityWeights X) (F : X → Y) (D g : X → ℝ)
    (hD0 : ∀ x, 0 ≤ D x) (hD : 0 < p.mean D) {C ε a : ℝ}
    (ha : 0 < a) (hlower : a ≤ p.mean D) (hg : ∀ x, g x ≤ C)
    (he : ∀ G : Finset Y, |p.mean (fun x => D x * (if F x ∈ G then 1 else 0)) -
      p.mean (fun x => g x * (if F x ∈ G then 1 else 0))| ≤ ε) :
    (p.fiberLaw F).excessMass ((p.reweightPositive D hD0 hD).fiberLaw F) (C / a) ≤ ε / a := by
  apply excessMass_le_of_mass_le
  intro G
  exact p.reweightPositive_fiber_mass_le F D g hD0 hD ha hlower hg G (he G)

end Erdos3.FiniteProbabilityWeights

end

end OAI
