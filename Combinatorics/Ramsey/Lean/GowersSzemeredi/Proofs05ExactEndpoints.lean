import GowersSzemeredi.Proofs05Corollary56Strong
import GowersSzemeredi.Proofs05Lemma9Scale
import GowersSzemeredi.Proofs05PhaseRemoval
import GowersSzemeredi.Proofs05Lemma14

/-!
# Exact endpoints of the polynomial-partition chain

The strong one-polynomial diameter estimate and the rounding-safe scale
schedule discharge the two analytic obligations isolated by the compiled
partition engines.  This file keeps the resulting numbered endpoints small
and makes their dependency chain explicit.
-/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

/-- **Corollary 5.6.** -/
theorem corollary_5_6_holds : corollary_5_6 :=
  corollary_5_6_holds_of_strong_diameter
    corollary_5_6_strong_diameter_holds

/-- **Corollary 5.7.** -/
theorem corollary_5_7_holds : corollary_5_7 :=
  corollary_5_7_holds_of_corollary_5_6 corollary_5_6_holds

/-- **Lemma 5.9.** -/
theorem lemma_5_9_holds : lemma_5_9 :=
  lemma_5_9_holds_of_strong_diameter_and_scale_schedule
    corollary_5_6_strong_diameter_holds
    lemma_5_9_scale_schedule_holds

/-- **Lemma 5.14.** -/
theorem lemma_5_14_holds : lemma_5_14 :=
  lemma_5_14_holds_of_corollary_5_6 corollary_5_6_holds

end LeanProofs.GowersSzemeredi
