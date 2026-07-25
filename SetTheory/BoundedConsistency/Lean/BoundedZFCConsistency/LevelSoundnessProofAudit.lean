import BoundedZFCConsistency.LevelSoundnessProof

/-!
# Kernel audit for fixed-level soundness

This deliberately small module checks the public interface of
`BoundedZFCConsistency.LevelSoundnessProof` and prints the axioms of its
substantive theorems.  Keeping the audit separate prevents diagnostic output
from becoming part of the library-facing module.

The last section is the point of the audit.  `levelSoundnessAt` discharges
`BoundedZFCConsistency.LevelSoundness.LevelSoundnessAt` outright, so it must be
seen to rest on nothing beyond the ambient classical axioms — in particular on
no residual soundness or two-valuedness hypothesis.  With it and with
`LevelTwoValuedAt`, already closed by `BoundedZFCConsistency.LevelCollapse`, the
project's only remaining obligation about a single model is `AxiomCodesTrueAt`,
which `noBoundedRefutationAtLevel` still takes as a premise.
-/

namespace LeanProofs.BoundedZFCConsistency.LevelSoundnessProofAudit

open SetTheory
open LeanProofs.BoundedZFCConsistency

/-! ## Reading one polarity off the other -/

#check @levelTrue_of_sigmaTrue
#check @levelTrue_of_piTrue
#check @piFalse_of_not_levelTrue

#print axioms levelTrue_of_sigmaTrue
#print axioms levelTrue_of_piTrue
#print axioms piFalse_of_not_levelTrue

/-! ## Coded contexts at a fixed level -/

#check @ctxLevelTrue_cons
#check @ctxLevelTrue_shift

#print axioms ctxLevelTrue_cons
#print axioms ctxLevelTrue_shift

/-! ## Soundness at one rank, and its definability -/

#check @LevelSoundAt
#check @fLevelTrueF
#check @fLevelTrueF_spec
#check @fCtxLevelTrueF
#check @fCtxLevelTrueF_spec
#check @fLevelSoundAtF
#check @fLevelSoundAtF_spec
#check @envLevelSound
#check @fLevelSoundBelowF
#check @fLevelSoundBelowF_spec

#print axioms fLevelTrueF_spec
#print axioms fCtxLevelTrueF_spec
#print axioms fLevelSoundAtF_spec
#print axioms fLevelSoundBelowF_spec

/-! ## The seventeen cases and the rank induction -/

#check @levelSoundAt_step
#check @levelSoundBelow
#check @levelSoundAt_all

#print axioms levelSoundAt_step
#print axioms levelSoundBelow
#print axioms levelSoundAt_all

/-! ## The obligation discharged, and the payoff -/

#check @levelSoundnessAt
#check @noBoundedRefutationAtLevel

#print axioms levelSoundnessAt
#print axioms noBoundedRefutationAtLevel

end LeanProofs.BoundedZFCConsistency.LevelSoundnessProofAudit
