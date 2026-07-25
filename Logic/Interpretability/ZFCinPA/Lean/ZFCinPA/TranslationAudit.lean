import ZFCinPA.Translation

/-!
# Kernel audit for the syntax translation and the numeralwise theorem

This deliberately small module checks the public interface of
`ZFCinPA.Translation` and prints the axioms of its substantive theorems.
Keeping the audit separate prevents diagnostic output from becoming part of
the library-facing module.
-/

namespace LeanProofs.ZFCinPA.TranslationAudit

open LeanProofs.ZFCinPA

/-! ## The syntax translation -/

#check @toSetVar
#check @toSet

/-! ## Satisfaction preservation -/

#check @val_toSetVar
#check @eval_toSet

/-! ## Bundle extraction -/

#check @modelsZF_of_modelsZFC
#check @modelsZ_of_modelsZFC
#check @sep_clause
#check @repl_clause
#check @choice_clause
#check @zfcAxioms_of_models

/-! ## The numeralwise theorem -/

#check @conZFCSet
#check @zfc_proves_conZFCSet

/-! ## Assumption audit

Foundation's completeness theorem and the repository's semantic core are both
classical, so `Classical.choice`, `propext` and `Quot.sound` are expected;
nothing beyond Lean's three standard axioms should appear, and in particular
no `sorry` and no theory-specific axiom. -/

#print axioms eval_toSet
#print axioms zfcAxioms_of_models
#print axioms zfc_proves_conZFCSet

end LeanProofs.ZFCinPA.TranslationAudit
