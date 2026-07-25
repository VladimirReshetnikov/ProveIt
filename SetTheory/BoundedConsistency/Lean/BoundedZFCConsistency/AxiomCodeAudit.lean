import BoundedZFCConsistency.AxiomCode

/-!
# Kernel audit for the axiom-code predicate and the sentence `Con_n(ZFC)`

This deliberately small module checks the public interface of
`BoundedZFCConsistency.AxiomCode` and prints the axioms of its substantive
theorems.  Keeping the audit separate prevents diagnostic output from becoming
part of the library-facing module.
-/

namespace LeanProofs.BoundedZFCConsistency.AxiomCodeAudit

/- The audited statements mention the assembled formulas of the module, so the
pretty printer needs more room than the default. -/
set_option maxRecDepth 8000

open SetTheory
open SetTheory.FirstOrderClassicalCompleteness
open LeanProofs.BoundedZFCConsistency

/-! ## Iterated internal successor -/

#check @vsuccIter
#check @vsuccIter_mem_omega
#check @vsuccIter_natV
#check @fSuccIterF
#check @fSuccIterF_spec

/-! ## The two-value shift maps -/

#check @succIterVals
#check @succIterVals_isVarMap
#check @succIterVals_apply
#check @twoMapN
#check @twoMapV
#check @twoMapV_isVarMap
#check @twoMapV_zero
#check @twoMapV_one
#check @twoMapV_succ_succ
#check @twoMapV_agreesWith

#check @IsTwoMap
#check @isTwoMap_twoMapV
#check @isTwoMap_unique
#check @isTwoMap_iff
#check @fTwoMapF
#check @fTwoMapF_spec

/-! ## The four schema renamings, internally -/

#check @rsep_eq
#check @rf1_eq
#check @rf2_eq
#check @ri_eq

#check @rsepV
#check @rf1V
#check @rf2V
#check @riV
#check @rsepV_isVarMap
#check @rf1V_isVarMap
#check @rf2V_isVarMap
#check @riV_isVarMap
#check @rsepV_agreesWith
#check @rf1V_agreesWith
#check @rf2V_agreesWith
#check @riV_agreesWith

#check @renameV_rsepV_formCode
#check @renameV_rf1V_formCode
#check @renameV_rf2V_formCode
#check @renameV_riV_formCode

#check @fRsepMapF
#check @fRsepMapF_spec
#check @fRf1MapF
#check @fRf1MapF_spec
#check @fRf2MapF
#check @fRf2MapF_spec
#check @fRiMapF
#check @fRiMapF_spec

/-! ## Template codes -/

#check @tmplCode
#check @markerFree
#check @tmplCode_eq_formCode
#check @fTmplCodeF
#check @fTmplCodeF_spec
#check @fCodeOfF
#check @fCodeOfF_spec

/-! ## Internal code constructors -/

#check @impCodeV
#check @andCodeV
#check @iffCodeV
#check @allCodeV
#check @exCodeV
#check @impCodeV_isFormCodeSem
#check @andCodeV_isFormCodeSem
#check @iffCodeV_isFormCodeSem
#check @allCodeV_isFormCodeSem
#check @exCodeV_isFormCodeSem

/-! ## The schema instance codes -/

#check @SepSkel
#check @FuncSkel
#check @ImageSkel
#check @ReplSkel
#check @sepCodeVOf
#check @replCodeVOf
#check @sepCodeV
#check @replCodeV
#check @sepCodeVOf_eq
#check @replCodeVOf_eq
#check @sepCodeV_formCode
#check @replCodeV_formCode
#check @sepCodeV_isFormCodeSem
#check @replCodeV_isFormCodeSem
#check @fSepCodeF
#check @fSepCodeF_spec
#check @fReplCodeF
#check @fReplCodeF_spec

/-! ## The axiom-code predicate -/

#check @IsZFCAxiomCode
#check @fZFCAxiomCodeF
#check @fZFCAxiomCodeF_spec
#check @isZFCAxiomCode_of_ZFCax

#check @CtxZFCAxioms
#check @fCtxZFCAxiomsF
#check @fCtxZFCAxiomsF_spec
#check @ctxZFCAxioms_nil
#check @ctxZFCAxioms_ctxCode

/-! ## The sentence and the endpoint bridge -/

#check @conZFCBodyF
#check @conZFCBodyF_spec
#check @conZFCForm
#check @sentence_conZFCForm
#check @sat_conZFCForm_iff
#check @no_bounded_refutation_nil_of_conZFC
#check conZFCForm_semanticConsequence
#check @zfcprov_conZFCForm_of_valid
#check @zfcprov_conZFCForm_of_no_bounded_refutation

/-! ## Assumption audit

The internal set operators of `ZF.Zf` are carved out with `Exists.choose`, and
`renameV` is a conditional choice in the style of `applyV`, so
`Classical.choice` is expected throughout.  Nothing beyond Lean's three standard
axioms should appear, and in particular no `sorry`, no `native_decide`, and no
theory-specific axiom.

The ones that matter are: `isTwoMap_iff`, which is what lets a `Form` describe a
model-dependent variable map at all; `fTmplCodeF_spec` and
`tmplCode_eq_formCode`, the two halves of the template-code layer;
`sepCodeV_formCode` and `replCodeV_formCode`, the agreement of the internal
schema constructors with quotation; `fZFCAxiomCodeF_spec`, the exact
satisfaction spec of the axiom-code predicate, where a hidden assumption would
show up; `isZFCAxiomCode_of_ZFCax`, the one direction of agreement with the
external axiom set that is true — the converse is false in nonstandard models
and is not stated; and `sat_conZFCForm_iff` together with
`zfcprov_conZFCForm_of_no_bounded_refutation`, which are the statement of the
target and its reduction to a single semantic obligation. -/

#print axioms vsuccIter_natV
#print axioms fSuccIterF_spec
#print axioms succIterVals_apply

#print axioms twoMapV_zero
#print axioms twoMapV_one
#print axioms twoMapV_succ_succ
#print axioms twoMapV_agreesWith
#print axioms isTwoMap_twoMapV
#print axioms isTwoMap_unique
#print axioms isTwoMap_iff
#print axioms fTwoMapF_spec

#print axioms rsep_eq
#print axioms rf1_eq
#print axioms rf2_eq
#print axioms ri_eq
#print axioms rsepV_agreesWith
#print axioms renameV_rsepV_formCode
#print axioms renameV_rf1V_formCode
#print axioms renameV_rf2V_formCode
#print axioms renameV_riV_formCode
#print axioms fRsepMapF_spec
#print axioms fRf1MapF_spec
#print axioms fRf2MapF_spec
#print axioms fRiMapF_spec

#print axioms tmplCode_eq_formCode
#print axioms fTmplCodeF_spec
#print axioms fCodeOfF_spec

#print axioms sepCodeVOf_eq
#print axioms replCodeVOf_eq
#print axioms sepCodeV_formCode
#print axioms replCodeV_formCode
#print axioms sepCodeV_isFormCodeSem
#print axioms replCodeV_isFormCodeSem
#print axioms fSepCodeF_spec
#print axioms fReplCodeF_spec

#print axioms fZFCAxiomCodeF_spec
#print axioms isZFCAxiomCode_of_ZFCax
#print axioms fCtxZFCAxiomsF_spec
#print axioms ctxZFCAxioms_nil
#print axioms ctxZFCAxioms_ctxCode

#print axioms conZFCBodyF_spec
#print axioms sentence_conZFCForm
#print axioms sat_conZFCForm_iff
#print axioms no_bounded_refutation_nil_of_conZFC
#print axioms conZFCForm_semanticConsequence
#print axioms zfcprov_conZFCForm_of_valid
#print axioms zfcprov_conZFCForm_of_no_bounded_refutation

end LeanProofs.BoundedZFCConsistency.AxiomCodeAudit
