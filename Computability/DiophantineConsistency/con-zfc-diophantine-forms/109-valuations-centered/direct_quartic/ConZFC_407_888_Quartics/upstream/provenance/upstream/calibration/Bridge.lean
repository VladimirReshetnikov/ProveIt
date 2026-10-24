import DiophantineConsistency.Computability
import BusyBeaver.ZFC.KEndpoint

namespace DiophantineConsistency

open SetTheory SetTheory.BusyBeaver.ZFC
open LeanProofs.BoundedZFCConsistency
open EnumPerm Code254 KCode222

/-- This is syntactic consistency, for the repository's actual ZFC axiom set. -/
def ConZFC : Prop := ¬ BProv ZFCax_s [] Form.fBot

theorem halts_iff_refutation : HaltsFrom initialState ↔ BProv ZFCax_s [] Form.fBot :=
  (EnumPerm.halts_iff (s := initialState) rfl ⟨C222.truth, C222.truth, good_zero⟩).trans
    (KEndpoint.c222_iff_zf_refutation.trans
      ConstructibleChoice.zf_refutation_iff_zfc_refutation)

/-- Exact syntactic ZFC inconsistency, as a constant recursively enumerable set. -/
def zfcRefutationInputs : Set ℕ := fun _ => BProv ZFCax_s [] Form.fBot

theorem zfcRefutationInputs_re : REPred zfcRefutationInputs :=
  refutationInputs_re.of_eq fun _ =>
    KEndpoint.c222_iff_zf_refutation.trans
      ConstructibleChoice.zf_refutation_iff_zfc_refutation

/-- The bounded arithmetic test accepts some bound exactly when the actual
ZFC axiom predicate has a finite refutation. -/
theorem exists_haltingTest_eq_one_iff_refutation :
    (∃ t, haltingTest t = 1) ↔ BProv ZFCax_s [] Form.fBot :=
  exists_haltingTest_eq_one_iff.trans
    (KEndpoint.c222_iff_zf_refutation.trans
      ConstructibleChoice.zf_refutation_iff_zfc_refutation)

end DiophantineConsistency
