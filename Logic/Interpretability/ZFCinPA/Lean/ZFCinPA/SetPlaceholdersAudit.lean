import ZFCinPA.SetPlaceholders

/-!
# Kernel audit for the indexed set-placeholder translation

This deliberately small module checks the public interface of
`ZFCinPA.SetPlaceholders` and prints the axioms of its substantive
theorems.  Keeping the audit separate prevents diagnostic output from
becoming part of the library-facing module.
-/

set_option autoImplicit false

namespace LeanProofs.ZFCinPA.SetPlaceholdersAudit

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA
open LeanProofs.ZFCinPA.SetPlaceholders

/-! ## The indexed placeholder language -/

#check @multiPlaceholderLanguage
#check (inferInstance :
  (multiPlaceholderLanguage 3 ![3, 1, 1]).DecidableEq)
#check (inferInstance :
  (setTemplateLanguage 3 ![3, 1, 1]).DecidableEq)
#check @placeholderRel
#check @setHom
#check @mainWithUnaryParams

/-! ## The translation and the compiler record -/

#check @translateTerm
#check @translateFormula
#check @translateTerm_shift
#check @translateTerm_bShift
#check @translateTerm_subst
#check @translateFormula_neg
#check @translateFormula_shift
#check @translateFormula_subst
#check @translateFormula_free
#check @setTemplateTranslation
#check @translateTerm_lMap_set
#check @translateFormula_lMap_set
#check @translateFormula_lMap_set_emb

/-! ## Source atoms and specialized shapes -/

#check @srcMem
#check @srcEq
#check @srcP
#check @liftSet
#check @translateFormula_imp
#check @translateFormula_iff
#check @translateFormula_emb_liftSet
#check @translate_emb_srcMem
#check @translate_emb_srcEq
#check @translate_emb_srcP

/-! ## The lifted theory and its compilation -/

#check @templateZFC
#check @templateZFCTranslation
#check @compileSetTemplate
#check @compileSetTemplate_isZFCProof

/-! ## Smoke test: the compiler elaborates over `ℕ` at the canonical
arity tuple (one ternary main predicate, two unary parameters) -/

#check fun (Ks : (i : Fin 3) →
      Bootstrapping.Semiformula ℕ ℒₛₑₜ ((![3, 1, 1] : Fin 3 → ℕ) i))
    (hKs : ∀ i, Bootstrapping.shift ℒₛₑₜ (Ks i).val = (Ks i).val)
    (σ : Sentence (setTemplateLanguage 3 ![3, 1, 1]))
    (d : templateZFC 3 ![3, 1, 1] ⊢! σ) =>
  compileSetTemplate Ks hKs d

/-! ## Assumption audit

Everything is built on Foundation's classical development, so
`Classical.choice` is expected throughout; nothing beyond Lean's three
standard axioms should appear — in particular no `sorry` and no
theory-specific axiom. -/

#print axioms translateFormula_shift
#print axioms translateFormula_subst
#print axioms translateFormula_free
#print axioms translateFormula_lMap_set_emb
#print axioms translate_emb_srcP
#print axioms compileSetTemplate
#print axioms compileSetTemplate_isZFCProof

end LeanProofs.ZFCinPA.SetPlaceholdersAudit
