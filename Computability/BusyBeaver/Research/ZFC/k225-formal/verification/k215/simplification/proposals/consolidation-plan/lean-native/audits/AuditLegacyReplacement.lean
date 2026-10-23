import BusyBeaver.ZFC.KQ1Replacement
import BusyBeaver.ZFC.InductiveAttempts
import BusyBeaver.ZFC.KQ1ReplacementNative

open SetTheory.BusyBeaver.ZFC

#check @KQ1Replacement.replacementRename
#check @KQ1Replacement.replacementChoiceForm
#check @KQ1Replacement.equalityFree_replacementChoiceForm
#check @KQ1Replacement.sat_replacementChoiceForm
#check @KQ1Replacement.replacement_instance
#check @KQ1Replacement.interpreted_replacement
#check @KQ1Replacement.quotient_relOf
#check @KQ1Replacement.quotient_replacement
#check @KQ1Replacement.quotient_repl_form

#print axioms KQ1Replacement.quotient_replacement
#print axioms KQ1Replacement.quotient_repl_form

/-- The new proof inhabits the exact type of the old theorem. -/
example : @KQ1ReplacementNative.quotient_replacement = @KQ1Replacement.quotient_replacement := rfl
example : @KQ1ReplacementNative.quotient_repl_form = @KQ1Replacement.quotient_repl_form := rfl

#print axioms InductiveAttempts.quotient_infinity
#print axioms InductiveAttempts.ordinary_infinity_of_container
