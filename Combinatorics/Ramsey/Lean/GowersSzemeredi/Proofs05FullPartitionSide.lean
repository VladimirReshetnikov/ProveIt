import GowersSzemeredi.Proofs05FullPartition
import GowersSzemeredi.Proofs05Lemma9Scale
import GowersSzemeredi.Proofs05Lemma14Side
import GowersSzemeredi.Proofs05PhaseRemovalSide

/-! Declarations of `Proofs05FullPartition` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

/-- Corollary 5.7: remove a polynomial phase on each target-length cell. -/
theorem corollary_5_7_holds : corollary_5_7 :=
  corollary_5_7_holds_of_corollary_5_6 corollary_5_6_holds

/-- Lemma 5.14: global phase removal over an input progression partition. -/
theorem lemma_5_14_holds : lemma_5_14 :=
  lemma_5_14_holds_of_corollary_5_6 corollary_5_6_holds

end LeanProofs.GowersSzemeredi

namespace LeanProofs.GowersSzemeredi

/-- Lemma 5.9: simultaneous target-length polynomial partitioning. -/
theorem lemma_5_9_holds : lemma_5_9 :=
  lemma_5_9_holds_of_strong_diameter_and_scale_schedule
    corollary_5_6_strong_diameter_holds lemma_5_9_scale_schedule_holds

end LeanProofs.GowersSzemeredi
