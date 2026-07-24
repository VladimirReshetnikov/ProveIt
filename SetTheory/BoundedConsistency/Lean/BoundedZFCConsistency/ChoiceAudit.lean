import BoundedZFCConsistency.Choice

/-!
# Kernel audit for the choice axiom and the ZFC axiom set

This deliberately small module checks the public interface of
`BoundedZFCConsistency.Choice` and prints the axioms of its substantive
theorems.  Keeping the audit separate prevents diagnostic output from becoming
part of the library-facing module.
-/

namespace LeanProofs.BoundedZFCConsistency.ChoiceAudit

open SetTheory
open LeanProofs.BoundedZFCConsistency

/-! ## The choice axiom as a formula -/

#check @fNot
#check @Choice_nonempty
#check @Choice_disjoint
#check @Choice_selector
#check @Choice_form
#check @Sentence_Choice_form

/-! ## The semantic principle and its bridge -/

#check @ChoiceSem
#check @bridge_Choice
#check @bridge_Choice_fwd
#check @bridge_Choice_sealed

/-! ## The ZFC axiom set -/

#check @ZFCax
#check @ZFCprov
#check @ZFCax_s
#check @Sentences_ZFC
#check @ZFCax_of_ZFax
#check @ZFCax_s_of_ZFax_s
#check @ZFCax_Choice
#check @ZFCax_s_Choice
#check @ZFCprov_of_ZFprov
#check @ZFCprov_Choice

/-! ## Assumption audit -/

#print axioms Sentence_Choice_form
#print axioms bridge_Choice
#print axioms bridge_Choice_sealed
#print axioms Sentences_ZFC
#print axioms ZFCprov_of_ZFprov
#print axioms ZFCprov_Choice

end LeanProofs.BoundedZFCConsistency.ChoiceAudit
