import BoundedZFCConsistency.UniverseTruthLevel

/-!
# Kernel audit for the externally indexed truth predicates

This deliberately small module checks the public interface of
`BoundedZFCConsistency.UniverseTruthLevel` and prints the axioms of its
substantive theorems.  Keeping the audit separate prevents diagnostic output
from becoming part of the library-facing module.
-/

namespace LeanProofs.BoundedZFCConsistency.UniverseTruthLevelAudit

open SetTheory
open LeanProofs.BoundedZFCConsistency

/-! ## The shift on universe environments -/

#check @econs_isUnivEnv
#check @econs_apply_zero
#check @econs_apply_succ

/-! ## The two oriented bounds -/

#check @SigmaBounded
#check @PiBounded
#check @fSigmaBoundedF
#check @fSigmaBoundedF_spec
#check @fPiBoundedF
#check @fPiBoundedF_spec
#check @quantBounded_of_sigmaBounded
#check @quantBounded_of_piBounded
#check @sigmaBounded_formCode_iff
#check @piBounded_formCode_iff
#check @not_piBounded_zero_all
#check @not_sigmaBounded_zero_ex

/-! ## Quantifier-free truth as a `Form` -/

#check @fQFTrueF
#check @fQFTrueF_spec

/-! ## The local step -/

#check @LevelJustified
#check @fLevelImpF
#check @fLevelImpF_spec
#check @fLevelAndF
#check @fLevelAndF_spec
#check @fLevelOrF
#check @fLevelOrF_spec
#check @fLevelAllF
#check @fLevelAllF_spec
#check @fLevelExF
#check @fLevelExF_spec
#check @fLevelJustifiedF
#check @fLevelJustifiedF_spec
#check @levelJustified_mono
#check @levelJustified_bit
#check @levelJustified_of_tag_low
#check @levelJustified_imp
#check @levelJustified_and
#check @levelJustified_or
#check @levelJustified_all
#check @levelJustified_ex

/-! ## Certificates -/

#check @LevelClosed
#check @fLevelClosedF
#check @fLevelClosedF_spec
#check @levelClosed_empty
#check @levelClosed_cup
#check @levelClosed_insert

/-! ## The externally indexed family

The level is a metatheoretic `Nat` in both recursions, and in neither is it a
de Bruijn slot: `levelSatF` maps a `Nat` to a `Form`, so each level is a
separate formula and no single formula defines truth for all levels. -/

#check @LevelSat
#check @levelSat_zero_iff
#check @levelSat_succ_iff
#check @levelSatF
#check @levelSatF_spec
#check @SigmaTrue
#check @PiFalse
#check @PiTrue
#check @fSigmaTrueF
#check @fSigmaTrueF_spec
#check @fPiFalseF
#check @fPiFalseF_spec
#check @fPiTrueF
#check @fPiTrueF_spec

/-! ## Subsumption, two-valuedness, level zero -/

#check @levelSat_succ_of_justified
#check @levelSat_succ_of_levelSat
#check @levelSat_mono
#check @sigmaTrue_mono
#check @piFalse_mono
#check @piTrue_anti
#check @levelSat_bit
#check @sigmaTrue_zero_iff
#check @piTrue_zero_iff
#check @sigmaTrue_not_piFalse_zero

/-! ## The Tarski clauses -/

#check @sigmaTrue_memAtom
#check @sigmaTrue_eqAtom
#check @sigmaTrue_bot
#check @piFalse_bot
#check @sigmaTrue_and_elim
#check @sigmaTrue_and_intro
#check @sigmaTrue_and
#check @piFalse_and_elim
#check @piFalse_and_intro
#check @piFalse_and
#check @sigmaTrue_or_elim
#check @sigmaTrue_or_intro
#check @sigmaTrue_or
#check @piFalse_or_elim
#check @piFalse_or_intro
#check @piFalse_or
#check @sigmaTrue_imp_elim
#check @sigmaTrue_imp_intro
#check @sigmaTrue_imp
#check @piFalse_imp_elim
#check @piFalse_imp_intro
#check @piFalse_imp
#check @sigmaTrue_ex_elim
#check @sigmaTrue_ex_intro
#check @sigmaTrue_ex
#check @piFalse_all_elim
#check @piFalse_all_intro
#check @piTrue_all

/-! ## The polarity switch -/

#check @sigmaTrue_all_of_piTrue
#check @piFalse_ex_of_not_sigmaTrue
#check @sigmaTrue_all_inv
#check @piFalse_ex_inv
#check @not_sigmaTrue_one_all
#check @not_piFalse_one_ex

/-! ## Agreement with the metatheory -/

#check @levelSat_formCode_zero
#check @sigmaTrue_formCode_of_sat
#check @piFalse_formCode_of_not_sat

/-! ## Assumption audit

The internal set operators of `ZF.Zf` are carved out with `Exists.choose`, the
Separation and Replacement images inherit that, and `vbit` branches on an
arbitrary proposition, so `Classical.choice` is expected throughout; nothing
beyond Lean's three standard axioms should appear, and in particular no
`sorry`, no `native_decide`, and no theory-specific axiom.

The ones that matter are `levelSatF_spec`, the unconditional `iff` between the
externally built formula and the relation at every fixed level, where a hidden
assumption would show up; the two polarity-switch introductions, which are the
only place two levels meet; the two level-one degeneracies, which certify that
the hierarchy does not collapse at its first positive stage; and the Tarski
clauses, which are the interface later modules consume. -/

#print axioms econs_isUnivEnv
#print axioms econs_apply_zero
#print axioms econs_apply_succ

#print axioms fSigmaBoundedF_spec
#print axioms fPiBoundedF_spec
#print axioms quantBounded_of_sigmaBounded
#print axioms quantBounded_of_piBounded
#print axioms sigmaBounded_formCode_iff
#print axioms piBounded_formCode_iff
#print axioms not_piBounded_zero_all
#print axioms not_sigmaBounded_zero_ex

#print axioms fQFTrueF_spec

#print axioms fLevelImpF_spec
#print axioms fLevelAndF_spec
#print axioms fLevelOrF_spec
#print axioms fLevelAllF_spec
#print axioms fLevelExF_spec
#print axioms fLevelJustifiedF_spec
#print axioms levelJustified_mono
#print axioms levelJustified_bit
#print axioms levelJustified_of_tag_low
#print axioms levelJustified_imp
#print axioms levelJustified_and
#print axioms levelJustified_or
#print axioms levelJustified_all
#print axioms levelJustified_ex

#print axioms fLevelClosedF_spec
#print axioms levelClosed_empty
#print axioms levelClosed_cup
#print axioms levelClosed_insert

#print axioms levelSatF_spec
#print axioms fSigmaTrueF_spec
#print axioms fPiFalseF_spec
#print axioms fPiTrueF_spec

#print axioms levelSat_succ_of_justified
#print axioms levelSat_succ_of_levelSat
#print axioms levelSat_mono
#print axioms sigmaTrue_mono
#print axioms piFalse_mono
#print axioms piTrue_anti
#print axioms levelSat_bit
#print axioms sigmaTrue_zero_iff
#print axioms piTrue_zero_iff
#print axioms sigmaTrue_not_piFalse_zero

#print axioms sigmaTrue_memAtom
#print axioms sigmaTrue_eqAtom
#print axioms sigmaTrue_bot
#print axioms piFalse_bot
#print axioms sigmaTrue_and
#print axioms piFalse_and
#print axioms sigmaTrue_or
#print axioms piFalse_or
#print axioms sigmaTrue_imp
#print axioms piFalse_imp
#print axioms sigmaTrue_ex
#print axioms piFalse_all_elim
#print axioms piFalse_all_intro
#print axioms piTrue_all

#print axioms sigmaTrue_all_of_piTrue
#print axioms piFalse_ex_of_not_sigmaTrue
#print axioms sigmaTrue_all_inv
#print axioms piFalse_ex_inv
#print axioms not_sigmaTrue_one_all
#print axioms not_piFalse_one_ex

#print axioms levelSat_formCode_zero
#print axioms sigmaTrue_formCode_of_sat
#print axioms piFalse_formCode_of_not_sat

end LeanProofs.BoundedZFCConsistency.UniverseTruthLevelAudit
