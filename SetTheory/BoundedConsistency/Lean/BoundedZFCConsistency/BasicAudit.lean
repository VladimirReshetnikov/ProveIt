import BoundedZFCConsistency.Basic

/-!
# Kernel audit for the quantifier-group-bounded set-theoretic calculus

This deliberately small module checks the public interface of
`BoundedZFCConsistency.Basic` and prints the axioms of its substantive
theorems.  Keeping the audit separate prevents diagnostic output from becoming
part of the library-facing module.
-/

namespace LeanProofs.BoundedZFCConsistency.BasicAudit

open SetTheory
open LeanProofs.BoundedZFCConsistency

/-! ## Ranks -/

#check @sigmaRank
#check @piRank
#check @quantifierGroups
#check @QuantifierBounded
#check @rankAtom

#check @hierarchyRanks_rename
#check @sigmaRank_rename
#check @piRank_rename
#check @quantifierGroups_rename
#check @quantifierBounded_rename_iff
#check @quantifierGroups_bot
#check @quantifierBounded_bot
#check @quantifierBounded_mono

#check @quantifierGroups_existential_atom
#check @quantifierGroups_universal_atom
#check @quantifierGroups_mixed_branches
#check @quantifierGroups_implication_polarity
#check @quantifierGroups_bounded_shape

/-! ## Proof trees and the every-occurrence rank -/

#check @contextRank
#check @nodeRank
#check @ProvTree
#check @ProvTree.erase
#check @ProvTree.occurrenceRank
#check @proofOccurrenceRank
#check @eraseProvTree
#check @provTree_complete

/-! ## Restricted provability -/

#check @ProofAllBounded
#check @RestrictedProv
#check @RestrictedBProv
#check @restrictedProv_erase
#check @restrictedBProv_erase
#check @proofAllBounded_mono
#check @restrictedProv_mono
#check @restrictedBProv_mono
#check @restrictedProv_cofinal
#check @restrictedBProv_cofinal

/-! ## The conclusion-only collapse -/

#check @ConclusionRestrictedProv
#check @ConclusionRestrictedBProv
#check @conclusionRestrictedProv_bot_iff
#check @conclusionRestrictedBProv_bot_iff

/-! ## The ZF instantiation -/

#check @RestrictedZFprov
#check @restrictedZFprov_erase
#check @restrictedZFprov_mono
#check @restrictedZFprov_cofinal

/-! ## Assumption audit

`Exists.choose` in `restrictedProv_erase` is the only place where classical
choice is used essentially; everything else is expected to be kernel-clean
apart from Lean's three standard axioms. -/

#print axioms hierarchyRanks_rename
#print axioms quantifierBounded_mono
#print axioms ProvTree.erase
#print axioms eraseProvTree
#print axioms provTree_complete
#print axioms restrictedProv_erase
#print axioms restrictedBProv_erase
#print axioms restrictedProv_mono
#print axioms restrictedBProv_mono
#print axioms restrictedProv_cofinal
#print axioms restrictedBProv_cofinal
#print axioms conclusionRestrictedProv_bot_iff
#print axioms conclusionRestrictedBProv_bot_iff
#print axioms restrictedZFprov_erase
#print axioms restrictedZFprov_cofinal

end LeanProofs.BoundedZFCConsistency.BasicAudit
