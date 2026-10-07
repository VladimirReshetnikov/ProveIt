import OAI.Combinatorics.Progressions.Linear.ProductKernelPairing

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Y : ι → Type*} [∀ i, Fintype (Y i)]

theorem productMean_mix_laws (p q : ∀ i, FiniteProbabilityWeights (Y i))
    (S : Finset ι) (f : (∀ i, Y i) → ℝ) :
    (FiniteProbabilityWeights.pi p).mean (fun x => (FiniteProbabilityWeights.pi q).mean
      (fun y => f (productCoordinateMix S x y))) =
      (FiniteProbabilityWeights.pi (fun i => if i ∈ S then p i else q i)).mean f := by
  rw [← productJoint_mean p (fun i _ => q i) (fun x y => f (productCoordinateMix S x y))]
  have h : ∀ i (g : Y i → ℝ), ((p i).joint (fun _ => q i)).mean
      (fun z => g (if i ∈ S then z.1 else z.2)) =
        (if i ∈ S then p i else q i).mean g := by
    intro i g
    by_cases hi : i ∈ S
    · simp only [hi, ite_true, FiniteProbabilityWeights.joint_mean, FiniteProbabilityWeights.mean_const]
    · simp only [hi, ite_false, FiniteProbabilityWeights.joint_mean, FiniteProbabilityWeights.mean_const]
  unfold productCoordinateMix
  exact productMean_coordinate_transport (fun i => (p i).joint (fun _ => q i))
      (fun i => if i ∈ S then p i else q i)
      (fun i (z : Y i × Y i) => if i ∈ S then z.1 else z.2) h f

end Erdos3

end

end OAI
