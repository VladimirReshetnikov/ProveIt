import BoundedZFCConsistency.AxiomTruth

/-!
# Kernel audit for truth of the internal ZFC axiom codes

This deliberately small module checks the public interface of
`BoundedZFCConsistency.AxiomTruth` and prints the axioms of its substantive
theorems.  Keeping the audit separate prevents diagnostic output from becoming
part of the library-facing module.

Three things are what the audit is for.

`axiomCodesTrueAt` discharges
`BoundedZFCConsistency.LevelSoundness.AxiomCodesTrueAt`, the last of the three
obligations that module names, so it must be seen to rest on nothing beyond the
ambient classical axioms — in particular on no residual axiom-truth,
two-valuedness or soundness hypothesis.  Its hypothesis is the *semantic* bundle
`ZFCAxioms`, which is a structure and therefore visible in the statement rather
than in the assumption list.

`sigmaTrue_sepCodeV` and `sigmaTrue_replCodeV` are the two schema clauses.  Both
quantify over an *internal* code, so both cover the nonstandard instances the
internal axiom set contains and which quote no external formula; neither carries
a hypothesis restricting the code to a quotation.

`zfcprov_conZFCForm` is the project's target.  It has no hypothesis at all: the
metatheoretic `n` is an ordinary argument, and the conclusion is an object-level
derivation from the sealed sentence theory `ZFCax_s`.  The three standard axioms
are expected — `Classical.choice` because the internal set operators of `ZF.Zf`
are carved out with `Exists.choose`, `Quot.sound` and `propext` because they are
everywhere — and nothing else may appear, in particular no `sorry` and no
`native_decide`.
-/

namespace LeanProofs.BoundedZFCConsistency.AxiomTruthAudit

open SetTheory
open LeanProofs.BoundedZFCConsistency

/-! ## The richer semantic bundle and the nine axioms -/

#check @ZFCAxioms
#check @sat_Ext_form
#check @sat_Pair_form
#check @sat_Union_form
#check @sat_Inf_form
#check @sat_Pow_form
#check @sat_Reg_form
#check @sat_Choice_form

#print axioms sat_Ext_form
#print axioms sat_Pair_form
#print axioms sat_Union_form
#print axioms sat_Inf_form
#print axioms sat_Pow_form
#print axioms sat_Reg_form
#print axioms sat_Choice_form

/-! ## The environment a universe environment induces -/

#check @univEnvOf
#check @univEnvOf_econs

#print axioms univEnvOf_econs

/-! ## Fixed-level truth of a quotation

`levelTruth_formCode` is the unconditional biconditional between the externally
indexed predicates and metatheoretic satisfaction, at every level bounding the
polarity rank.  A hidden assumption would show up here. -/

#check @levelTruth_formCode
#check @sigmaTrue_formCode_of_valid
#check @levelTrue_formCode_of_valid

#print axioms levelTruth_formCode
#print axioms sigmaTrue_formCode_of_valid
#print axioms levelTrue_formCode_of_valid

/-! ## Descent of the bound, and the composition identities -/

#check @piBounded_of_quantBounded_all
#check @compV_twoMapV
#check @compV_rsepV_econs
#check @compV_rf1V_econs
#check @compV_rf2V_econs
#check @compV_riV_econs

#print axioms piBounded_of_quantBounded_all
#print axioms compV_twoMapV
#print axioms compV_rsepV_econs
#print axioms compV_rf1V_econs
#print axioms compV_rf2V_econs
#print axioms compV_riV_econs

/-! ## The Separation schema

`sepSet` is `sepD` at the rendered truth predicate, which is the move the whole
hierarchy was built to license. -/

#check @fSepCondF
#check @envInstance
#check @fSepCondF_spec
#check @sepSet
#check @sepSet_spec
#check @sigmaTrue_sepCodeVOf
#check @sigmaTrue_sepCodeV

#print axioms fSepCondF_spec
#print axioms sepSet_spec
#print axioms sigmaTrue_sepCodeVOf
#print axioms sigmaTrue_sepCodeV

/-! ## The Replacement schema -/

#check @fReplRelF
#check @fReplRelF_spec
#check @sigmaTrue_replCodeVOf
#check @sigmaTrue_replCodeV

#print axioms fReplRelF_spec
#print axioms sigmaTrue_replCodeVOf
#print axioms sigmaTrue_replCodeV

/-! ## The obligation discharged, and the target -/

#check @axiomCodesTrueAt
#check @noBoundedRefutationAtLevel_zfc
#check @zfcAxioms_of_zfcModel
#check @conZFCForm_semanticConsequence_zfc
#check @zfcprov_conZFCForm

#print axioms axiomCodesTrueAt
#print axioms noBoundedRefutationAtLevel_zfc
#print axioms zfcAxioms_of_zfcModel
#print axioms conZFCForm_semanticConsequence_zfc
#print axioms zfcprov_conZFCForm

end LeanProofs.BoundedZFCConsistency.AxiomTruthAudit
