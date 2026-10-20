import BusyBeaver.ZFC.KLowerQHyp
import BusyBeaver.ZFC.KEndpoint221

/-!
**The 221-state machine halts iff ZF (equivalently ZFC) is inconsistent.**

The lower chain of the 222/221 calculus, semantically. Take for the completeness theorem
`KEind222.c222_complete` the named formulas whose interpreted codes are derivable
(`DerivableNF`). In any irreflexive model of them every equality-free relation has Elliot Glazer's
seed property (`seed_eqFree`); the indiscernibility quotient extends it to every relation
(`fullSeed_of_derivable`, `formSeed_of_fullSeed`); and the bisimulation quotient of the tagged
domain of such a model has a well-founded part satisfying ZF (`zf_consistent_of_formSeed`). So a
ZF refutation leaves no model: the code 1 is derivable (`c222_of_zf_refutation`). With the upper
bound (`KUpper222.zf_refutation_of_c222`) and the machine layers (`KEndpoint221`) this is the
endpoint.
-/

namespace SetTheory.BusyBeaver.ZFC.KLower221

open LeanProofs.BoundedZFCConsistency KSeed222 KIndisc222 KLower KDenseBridge KDense221

/-- **Lower chain.** A refutation of ZF makes the code 1 derivable. -/
theorem c222_of_zf_refutation (hf : BProv ZFax_s [] Form.fBot) : KCode222.C222 Code254.F := by
  apply KEind222.c222_complete DerivableNF (fun _ h => h)
  intro D mem hirr hT e
  have hfull := fullSeed_of_derivable mem hirr hT
  exact zf_consistent_of_formSeed (formSeed_of_fullSeed hfull) hfull.irr (KIndisc222.mk mem (e 0)) hf

/-- The 222/221 calculus derives the code 1 iff ZF is refutable. -/
theorem c222_iff_zf_refutation : KCode222.C222 Code254.F ↔ BProv ZFax_s [] Form.fBot :=
  ⟨KUpper222.zf_refutation_of_c222, c222_of_zf_refutation⟩

/-- **The 221-state machine halts on the blank tape iff ZF is refutable.** -/
theorem blank_halts_iff_zf_refutation : BlankHalts machine221 ↔ BProv ZFax_s [] Form.fBot :=
  KEndpoint221.blank_halts_iff_c222.trans c222_iff_zf_refutation

/-- **The 221-state machine halts on the blank tape iff ZFC is refutable.** -/
theorem blank_halts_iff_zfc_refutation : BlankHalts machine221 ↔ BProv ZFCax_s [] Form.fBot :=
  blank_halts_iff_zf_refutation.trans ConstructibleChoice.zf_refutation_iff_zfc_refutation

/-- **The 221-state machine runs forever iff ZFC is consistent.** -/
theorem nonhalting_iff_zfc_consistency : (¬ BlankHalts machine221) ↔ ¬ BProv ZFCax_s [] Form.fBot :=
  not_congr blank_halts_iff_zfc_refutation

#print axioms blank_halts_iff_zfc_refutation
#print axioms nonhalting_iff_zfc_consistency

end SetTheory.BusyBeaver.ZFC.KLower221
