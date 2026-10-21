import QuotientCalibration
import BusyBeaver.ZFC.KLowerQHyp

/-!
Full refutational calibration of quotient detachment.  The lower bound below
is the existing `KEndpoint.c222_of_zf_refutation` argument, followed by the
`Q222.base` constructor.  Importing its mathematical dependency directly
avoids pulling in unrelated tape simulation and state-allocation endpoints.
-/

namespace SetTheory.BusyBeaver.ZFC.QuotientEquivalence

open LeanProofs.BoundedZFCConsistency KSeed222 KIndisc222 KLower
open Quotient222 QuotientCalibration

/-- The original lower calibration embeds unchanged in the larger calculus. -/
theorem q222_of_zf_refutation (hf : BProv ZFax_s [] Form.fBot) :
    Q222 Code254.F := by
  apply Q222.base
  apply KEind222.c222_complete DerivableNF (fun _ h => h)
  intro D mem hirr hT e
  have hfull := fullSeed_of_derivable mem hirr hT
  exact zf_consistent_of_formSeed (formSeed_of_fullSeed hfull) hfull.irr
    (KIndisc222.mk mem (e 0)) hf

theorem q222_iff_zf_refutation : Q222 Code254.F ↔ BProv ZFax_s [] Form.fBot :=
  ⟨zf_refutation_of_q222, q222_of_zf_refutation⟩

/-- Exact consistency-level equivalence with the repository's ZFC calculus. -/
theorem q222_iff_zfc_refutation : Q222 Code254.F ↔ BProv ZFCax_s [] Form.fBot :=
  q222_iff_zf_refutation.trans ConstructibleChoice.zf_refutation_iff_zfc_refutation

#print axioms q222_of_zf_refutation
#print axioms q222_iff_zfc_refutation

end SetTheory.BusyBeaver.ZFC.QuotientEquivalence
