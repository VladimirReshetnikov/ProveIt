import ZFCinPA.SetCongruence

/-!
# Kernel audit for the internal `ℒₛₑₜ` equality replacement

This deliberately small module checks the public interface of
`ZFCinPA.SetCongruence` and prints the axioms of its substantive theorems.
The smoke test discharges the full translated congruence antecedent at the
canonical arity tuple `![3, 1, 1]` (ternary truth predicate plus two unary
parameter placeholders) over `ℕ`.
-/

set_option autoImplicit false

namespace LeanProofs.ZFCinPA.SetCongruenceAudit

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA
open LeanProofs.ZFCinPA.SetPlaceholders
open LeanProofs.ZFCinPA.SetPlaceholderQuotient
open LeanProofs.ZFCinPA.SetCongruence

/-! ## Internal symbol recognition -/

#check @setEqIndex
#check @setMemIndex
#check @isFunc_iff_Set
#check @isRel_iff_Set

/-! ## Typed atoms and seed laws -/

#check @eqAtom
#check @neAtom
#check @memAtom
#check @nmemAtom
#check @set_eq_refl
#check @set_eq_symm
#check @set_eq_uniform_trans
#check @subst_eq
#check @subst_mem
#check @subst_ne
#check @subst_nmem

/-! ## The replacement schema -/

#check @term_replace
#check @replace_eq
#check @replace_mem
#check @replace_ne
#check @replace_nmem
#check @replace_aux
#check @setReplace'
#check @setReplace

/-! ## The congruence formulas and their discharges -/

#check @leftTuple
#check @rightTuple
#check @congruenceContext
#check @congruenceFormula
#check @congruenceProof₀
#check @congruenceProof₁
#check @congruenceProof₂
#check @congruenceProof₃

/-! ## Translation and assembly -/

#check @relExt_eq_src
#check @translateFormula_allClosure
#check @translateFormula_conj
#check @translate_setPlaceholderCongruenceSentence
#check @translate_setPlaceholderCongruence
#check @translatedCongruenceProof

/-! ## Smoke test: the full discharge at the canonical arity tuple

At `arities = ![3, 1, 1]` every per-placeholder congruence law is supplied
by a concrete-arity discharge, so the entire translated congruence
antecedent is internally provable in `𝗭𝗙𝗖` at arbitrary (possibly
nonstandard) model-coded interpretations. -/

noncomputable example
    (Ks : (i : Fin 3) →
      Bootstrapping.Semiformula ℕ ℒₛₑₜ ((![3, 1, 1] : Fin 3 → ℕ) i)) :
    (𝗭𝗙𝗖 : SetTheory).internalize ℕ ⊢!
      translateFormula Ks
        (Rewriting.emb (setPlaceholderCongruence 3 ![3, 1, 1]) :
          Proposition (setTemplateLanguage 3 ![3, 1, 1])) :=
  (translatedCongruenceProof (𝗭𝗙𝗖 : SetTheory) Ks (fun i ↦
    match i with
    | 0 => congruenceProof₃ (𝗭𝗙𝗖 : SetTheory) (Ks 0)
    | 1 => congruenceProof₁ (𝗭𝗙𝗖 : SetTheory) (Ks 1)
    | 2 => congruenceProof₁ (𝗭𝗙𝗖 : SetTheory) (Ks 2))).get

/-! ## Assumption audit

Everything is built on Foundation's classical development, so
`Classical.choice` is expected throughout; nothing beyond Lean's three
standard axioms should appear — in particular no `sorry` and no
theory-specific axiom. -/

#print axioms isRel_iff_Set
#print axioms subst_eq
#print axioms setReplace
#print axioms congruenceProof₁
#print axioms congruenceProof₂
#print axioms congruenceProof₃
#print axioms translate_setPlaceholderCongruenceSentence
#print axioms translatedCongruenceProof

end LeanProofs.ZFCinPA.SetCongruenceAudit
