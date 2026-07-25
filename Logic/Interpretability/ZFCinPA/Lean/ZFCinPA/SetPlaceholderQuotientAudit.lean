import ZFCinPA.SetPlaceholderQuotient

/-!
# Kernel audit for the set-placeholder equality quotient

This deliberately small module checks the public interface of
`ZFCinPA.SetPlaceholderQuotient` and prints the axioms of its substantive
theorems.
-/

set_option autoImplicit false

namespace LeanProofs.ZFCinPA.SetPlaceholderQuotientAudit

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA
open LeanProofs.ZFCinPA.SetPlaceholders
open LeanProofs.ZFCinPA.SetPlaceholderQuotient

/-! ## The congruence sentences -/

#check @setPlaceholderCongruenceSentence
#check @setPlaceholderCongruence
#check @models_setPlaceholderCongruence_iff

/-! ## The equality completion -/

#check @models_fullEquality
#check @complete_underSetPlaceholderCongruence

/-! ## Smoke test: the completion elaborates at the canonical arity tuple -/

#check fun (σ : Sentence (setTemplateLanguage 3 ![3, 1, 1]))
    (H : ∀ (X : Type)
        [Nonempty X]
        [Structure (setTemplateLanguage 3 ![3, 1, 1]) X]
        [Structure.Eq (setTemplateLanguage 3 ![3, 1, 1]) X]
        [X↓[setTemplateLanguage 3 ![3, 1, 1]] ⊧* templateZFC 3 ![3, 1, 1]],
        X↓[setTemplateLanguage 3 ![3, 1, 1]] ⊧ σ) =>
  complete_underSetPlaceholderCongruence σ H

/-! ## Assumption audit

Everything is built on Foundation's classical development, so
`Classical.choice` is expected throughout; nothing beyond Lean's three
standard axioms should appear — in particular no `sorry` and no
theory-specific axiom. -/

#print axioms models_setPlaceholderCongruence_iff
#print axioms models_fullEquality
#print axioms complete_underSetPlaceholderCongruence

end LeanProofs.ZFCinPA.SetPlaceholderQuotientAudit
