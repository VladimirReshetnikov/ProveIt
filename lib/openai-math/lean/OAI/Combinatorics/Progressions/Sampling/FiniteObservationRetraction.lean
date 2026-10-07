import OAI.Combinatorics.Progressions.Probability.IntervalDivisorProbability

namespace OAI

section

namespace Erdos3

noncomputable def finiteObservation {X Z : Type*} (Q : Finset X) (hQ : Q.Nonempty)
    (ι : X → Z) : Z → Q := by
  letI : Nonempty Q := hQ.to_subtype
  exact Function.invFun (fun q : Q => ι q.val)

theorem finiteObservation_apply {X Z : Type*} (Q : Finset X) (hQ : Q.Nonempty)
    (ι : X → Z) (hι : Function.Injective ι) (q : Q) :
    finiteObservation Q hQ ι (ι q.val) = q := by
  let : Nonempty Q := hQ.to_subtype
  exact Function.leftInverse_invFun (hι.comp Subtype.val_injective) q

namespace FiniteProbabilityWeights

open scoped BigOperators Classical

theorem uniformFinset_weight {X : Type*} (Q : Finset X) (hQ : Q.Nonempty) (q : Q) :
    (uniformFinset Q hQ).weight q = (Q.card : ℝ)⁻¹ := by
  simp only [uniformFinset, uniform, Fintype.card_coe]

theorem fiberLaw_id {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X) :
    p.fiberLaw id = p := by
  apply eq_of_weight_eq
  intro x
  simp [fiberLaw_weight, fiberMean, mean, mul_ite, eq_comm]

theorem uniformFinset_observation_fiberLaw {X Z : Type*} (Q : Finset X) (hQ : Q.Nonempty)
    (ι : X → Z) (hι : Function.Injective ι) :
    (uniformFinset Q hQ).fiberLaw (fun q => finiteObservation Q hQ ι (ι q.val)) =
      uniformFinset Q hQ := by
  have he : (fun q : Q => finiteObservation Q hQ ι (ι q.val)) = id :=
    funext (fun q => finiteObservation_apply Q hQ ι hι q)
  rw [he, fiberLaw_id]

end FiniteProbabilityWeights
end Erdos3

end

end OAI
