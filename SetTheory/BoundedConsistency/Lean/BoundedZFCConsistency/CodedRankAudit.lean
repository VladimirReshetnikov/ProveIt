import BoundedZFCConsistency.CodedRank

/-!
# Kernel audit for the internal ranks, the bounded predicate, and `Con_n`

This deliberately small module checks the public interface of
`BoundedZFCConsistency.CodedRank` and prints the axioms of its substantive
theorems.  Keeping the audit separate prevents diagnostic output from becoming
part of the library-facing module.
-/

namespace LeanProofs.BoundedZFCConsistency.CodedRankAudit

/- The audited statements mention the assembled formulas of the module, so the
pretty printer needs more room than the default. -/
set_option maxRecDepth 8000

open SetTheory
open SetTheory.FirstOrderClassicalCompleteness
open LeanProofs.BoundedZFCConsistency

/-! ## The internal order, maximum and minimum -/

#check @LeN
#check @leN_iff
#check @leN_trans
#check @vmaxN
#check @vmaxN_of_mem
#check @vmaxN_of_not_mem
#check @vminN
#check @vminN_of_mem
#check @vminN_of_not_mem
#check @vmaxN_mem_omega
#check @vminN_mem_omega
#check @leN_vmaxN_left
#check @leN_vmaxN_right
#check @vminN_leN_left
#check @vminN_leN_right
#check @leN_vminN

/-! ### Agreement with the external order on numerals -/

#check @natV_mem_iff
#check @leN_natV_iff
#check @vmaxN_natV
#check @vminN_natV

/-! ### The object-language rendering of the order -/

#check @fLeF
#check @fLeF_spec
#check @fMaxF
#check @fMaxF_spec
#check @fMinF
#check @fMinF_spec

/-! ## The rank graph -/

#check @RankStep
#check @rankStep_mono
#check @RankClosed
#check @rankClosed_empty
#check @rankClosed_cup
#check @rankClosed_insert
#check @RankCertifies
#check @Ranks
#check @Ranks.mem_omega
#check @ranks_of_step

/-! ### Introduction and inversion -/

#check @ranks_memAtom
#check @ranks_eqAtom
#check @ranks_bot
#check @ranks_imp
#check @ranks_and
#check @ranks_or
#check @ranks_all
#check @ranks_ex

#check @ranks_memAtom_inv
#check @ranks_eqAtom_inv
#check @ranks_bot_inv
#check @ranks_imp_inv
#check @ranks_and_inv
#check @ranks_or_inv
#check @ranks_all_inv
#check @ranks_ex_inv

/-! ### The object-language rendering of the graph -/

#check @fRankAtomF
#check @fRankAtomF_spec
#check @fRankBotF
#check @fRankBotF_spec
#check @fRankImpF
#check @fRankImpF_spec
#check @fRankBinF
#check @fRankBinF_spec
#check @fRankAllF
#check @fRankAllF_spec
#check @fRankExF
#check @fRankExF_spec
#check @fRankStepF
#check @fRankStepF_spec
#check @fRankClosedF
#check @fRankClosedF_spec
#check @fRanksF
#check @fRanksF_spec

/-! ## Totality, single-valuedness, and quotation -/

#check @RankTotal
#check @fRankTotalF_spec
#check @rankTotal_of_isFormCodeSem
#check @RankUnique
#check @fRankUniqueF_spec
#check @rankUnique_of_isFormCodeSem
#check @ranks_formCode
#check @ranks_formCode_iff

/-! ## The bound on codes -/

#check @QuantBounded
#check @fQuantBoundedF
#check @fQuantBoundedF_spec
#check @quantBounded_formCode_iff
#check @quantBounded_of_le
#check @quantBounded_imp
#check @quantBounded_and
#check @quantBounded_or
#check @quantBounded_all
#check @quantBounded_ex

/-! ### Invariance under internal renaming -/

#check @RankRen
#check @fRankRenF_spec
#check @rankRen_of_isFormCodeSem
#check @quantBounded_of_renames

/-! ## The all-occurrences bound on a coded derivation -/

#check @CtxBounded
#check @fCtxBoundedF
#check @fCtxBoundedF_spec
#check @DerAllBounded
#check @fDerAllBoundedF
#check @fDerAllBoundedF_spec

#check @DerStepBounded
#check @derStep_of_derStepBounded
#check @quantBounded_of_derCite
#check @derStepBounded_of_derAllBounded

/-! ## The sentence and the endpoint bridge -/

#check @logicConBodyF
#check @conBodyF_spec
#check @logicConForm
#check @sentence_conForm
#check @sat_logicConForm_iff
#check @zfAxioms_of_zfcModel
#check logicConForm_semanticConsequence
#check @zfcprov_logicConForm_of_valid
#check @zfcprov_logicConForm_of_no_bounded_refutation

/-! ## Assumption audit

The internal set operators of `ZF.Zf` are carved out with `Exists.choose`, and
`vmaxN`, `vminN` are conditional choices in the style of `applyV` and
`renameV`, so `Classical.choice` is expected throughout.  Nothing beyond Lean's
three standard axioms should appear, and in particular no `sorry`, no
`native_decide`, and no theory-specific axiom.

The ones that matter are: the four unconditional `iff`s between a `Form` and
the property an induction carries — `fRanksF_spec`, `fRankTotalF_spec`,
`fRankUniqueF_spec`, `fRankRenF_spec` — where a hidden assumption would show
up; `rankTotal_of_isFormCodeSem` and `rankUnique_of_isFormCodeSem`, which make
the ranks a function of the code at all; `ranks_formCode_iff` and
`quantBounded_formCode_iff`, which are the whole agreement with the
metatheoretic ranks of `BoundedZFCConsistency.Basic`;
`derStepBounded_of_derAllBounded`, which is the every-occurrence claim; and
`sat_logicConForm_iff` with `zfcprov_logicConForm_of_no_bounded_refutation`, which are
the statement of the target and its reduction to a single semantic
obligation. -/

#print axioms leN_trans
#print axioms natV_mem_iff
#print axioms leN_natV_iff
#print axioms vmaxN_natV
#print axioms vminN_natV
#print axioms fMaxF_spec
#print axioms fMinF_spec

#print axioms rankStep_mono
#print axioms rankClosed_cup
#print axioms rankClosed_insert
#print axioms ranks_of_step
#print axioms ranks_imp
#print axioms ranks_all
#print axioms ranks_imp_inv
#print axioms ranks_all_inv

#print axioms fRankAtomF_spec
#print axioms fRankImpF_spec
#print axioms fRankBinF_spec
#print axioms fRankAllF_spec
#print axioms fRankExF_spec
#print axioms fRankStepF_spec
#print axioms fRankClosedF_spec
#print axioms fRanksF_spec

#print axioms fRankTotalF_spec
#print axioms rankTotal_of_isFormCodeSem
#print axioms fRankUniqueF_spec
#print axioms rankUnique_of_isFormCodeSem
#print axioms ranks_formCode
#print axioms ranks_formCode_iff

#print axioms fQuantBoundedF_spec
#print axioms quantBounded_formCode_iff
#print axioms quantBounded_imp
#print axioms quantBounded_and
#print axioms quantBounded_or
#print axioms quantBounded_all
#print axioms quantBounded_ex

#print axioms fRankRenF_spec
#print axioms rankRen_of_isFormCodeSem
#print axioms quantBounded_of_renames

#print axioms fCtxBoundedF_spec
#print axioms fDerAllBoundedF_spec
#print axioms derStep_of_derStepBounded
#print axioms derStepBounded_of_derAllBounded

#print axioms conBodyF_spec
#print axioms sentence_conForm
#print axioms sat_logicConForm_iff
#print axioms zfAxioms_of_zfcModel
#print axioms logicConForm_semanticConsequence
#print axioms zfcprov_logicConForm_of_valid
#print axioms zfcprov_logicConForm_of_no_bounded_refutation

end LeanProofs.BoundedZFCConsistency.CodedRankAudit
