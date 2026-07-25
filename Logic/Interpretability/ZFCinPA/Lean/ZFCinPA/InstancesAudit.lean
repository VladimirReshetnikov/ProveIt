import ZFCinPA.Instances
import ZFCinPA.SchemaClosure
import ZFCinPA.SeparationDelta1
import ZFCinPA.ReplacementDelta1
import ZFCinPA.ZFDelta1

/-!
# Kernel audit for the `ℒₛₑₜ` bootstrapping instances

This deliberately small module checks the public interface of the `ZFCinPA`
instance modules and prints the axioms of their substantive theorems.  Keeping
the audit separate prevents diagnostic output from becoming part of the
library-facing modules.
-/

namespace LeanProofs.ZFCinPA.InstancesAudit

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA

/-! ## The language instances -/

#check @set_mem_range_encode_func
#check @set_mem_range_encode_rel
#check @instLORDefinableSet
#check @instFiniteSet

#check (inferInstance : (ℒₛₑₜ).LORDefinable)
#check (inferInstance : (ℒₛₑₜ).Finite)

/-! ## The generic closure recognizer -/

#check @fvarVec_val_eq_lang
#check @subst_fvarVec_quote_lang
#check @freeVariables_empty_of_shift_fixed
#check @closure_inversion_lang
#check @SchemaRecognizer
#check @schemaRecognizer_quote_iff
#check @mem_range_univCl_iff

/-! ## The schema recognizers -/

#check @sepBodyMeta
#check @separationSchema_eq_univCl
#check @sepBody_quote
#check @sepBodyVal_quote
#check @le_sepBodyVal_quote
#check @sepBodyVal.defined
#check @separationTheory_delta1

#check @repBodyMeta
#check @replacementSchema_eq_univCl
#check @repBody_quote
#check @repBodyVal_quote
#check @le_repBodyVal_quote
#check @repBodyVal.defined
#check @replacementTheory_delta1

/-! ## The headline theory instances -/

#check @zf_eq
#check @eqAxiom_delta1
#check @zfFixed_delta1
#check @ZF_delta1
#check @AC_delta1
#check @ZFC_delta1

#check (inferInstance : (𝗭𝗙 : SetTheory).Δ₁)
#check (inferInstance : (𝗭𝗙𝗖 : SetTheory).Δ₁)

/-! ## Smoke tests: the coded-syntax and provability layers fire for `ℒₛₑₜ` -/

#check (Bootstrapping.IsFormula (V := ℕ) ℒₛₑₜ)

#check (⌜Axiom.choice⌝ : ℕ)

#check (Bootstrapping.Provable (V := ℕ) (T := (𝗭𝗙𝗖 : SetTheory)))

#check fun (σ : SetTheorySentence) (h : 𝗭𝗙𝗖 ⊢ σ) =>
  Bootstrapping.internalize_provability (V := ℕ) h

/-! ## Assumption audit

The recognizer formulas and the internal syntax operations are built on
Foundation's classical development, so `Classical.choice` is expected
throughout; nothing beyond Lean's three standard axioms should appear, and in
particular no `sorry` and no theory-specific axiom. -/

#print axioms instLORDefinableSet
#print axioms instFiniteSet
#print axioms closure_inversion_lang
#print axioms schemaRecognizer_quote_iff
#print axioms sepBodyVal_quote
#print axioms le_sepBodyVal_quote
#print axioms separationTheory_delta1
#print axioms repBodyVal_quote
#print axioms le_repBodyVal_quote
#print axioms replacementTheory_delta1
#print axioms zf_eq
#print axioms ZF_delta1
#print axioms ZFC_delta1

end LeanProofs.ZFCinPA.InstancesAudit
