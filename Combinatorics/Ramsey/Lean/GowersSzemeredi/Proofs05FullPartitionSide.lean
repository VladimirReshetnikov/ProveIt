import GowersSzemeredi.Proofs05FullPartition
import GowersSzemeredi.Proofs05Lemma9Scale

/-! Declarations of `Proofs05FullPartition` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

/-- Lemma 5.9: simultaneous target-length polynomial partitioning. -/
theorem lemma_5_9_holds : lemma_5_9 :=
  lemma_5_9_holds_of_strong_diameter_and_scale_schedule
    corollary_5_6_strong_diameter_holds lemma_5_9_scale_schedule_holds

end LeanProofs.GowersSzemeredi
