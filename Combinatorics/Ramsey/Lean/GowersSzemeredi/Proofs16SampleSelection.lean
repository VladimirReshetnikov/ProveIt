import GowersSzemeredi.Proofs16DistinctSampling

/-! # One simultaneous sample with controlled discarded mass

The same sample is used for every affine class. The estimate is weighted
by class sizes, so it controls discarded points rather than merely the
number of unsuccessful classes.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace LeanProofs.GowersSzemeredi

/-- Retain whole successful classes, including the sampled anchors. -/
def section16RetainedClass {α : Type*} {r : Nat}
    (C : Finset α) (sample : Fin r → α) : Finset α :=
  if section16SampleHasDistinctPair C sample then C else ∅

theorem section16RetainedClass_subset {α : Type*} {r : Nat}
    (C : Finset α) (sample : Fin r → α) : section16RetainedClass C sample ⊆ C := by
  unfold section16RetainedClass
  split_ifs <;> simp

theorem section16RetainedClass_anchors {α : Type*} {r : Nat}
    (C : Finset α) (sample : Fin r → α)
    (hne : (section16RetainedClass C sample).Nonempty) :
    section16SampleHasDistinctPair (section16RetainedClass C sample) sample := by
  unfold section16RetainedClass at *
  split_ifs with h
  · exact h
  · simp [h] at hne

end LeanProofs.GowersSzemeredi
