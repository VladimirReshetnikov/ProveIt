import ZFCinPA.SetCongruence

set_option autoImplicit false
noncomputable section

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA.SetPlaceholders
open LeanProofs.ZFCinPA.SetPlaceholderQuotient
open LeanProofs.ZFCinPA.SetCongruence

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

#print axioms LeanProofs.ZFCinPA.SetPlaceholderQuotient.models_setPlaceholderCongruence_iff
#print axioms LeanProofs.ZFCinPA.SetPlaceholderQuotient.models_fullEquality
#print axioms LeanProofs.ZFCinPA.SetPlaceholderQuotient.complete_underSetPlaceholderCongruence
#print axioms LeanProofs.ZFCinPA.SetCongruence.setReplace'
#print axioms LeanProofs.ZFCinPA.SetCongruence.setReplace
#print axioms LeanProofs.ZFCinPA.SetCongruence.congruenceProof₀
#print axioms LeanProofs.ZFCinPA.SetCongruence.congruenceProof₁
#print axioms LeanProofs.ZFCinPA.SetCongruence.congruenceProof₂
#print axioms LeanProofs.ZFCinPA.SetCongruence.congruenceProof₃
#print axioms LeanProofs.ZFCinPA.SetCongruence.translate_setPlaceholderCongruenceSentence
#print axioms LeanProofs.ZFCinPA.SetCongruence.translate_setPlaceholderCongruence
#print axioms LeanProofs.ZFCinPA.SetCongruence.translatedCongruenceProof

example (T : SetTheory) [T.Δ₁] [𝗘𝗤 ℒₛₑₜ ⪯ T]
    (K : Bootstrapping.Semiformula V ℒₛₑₜ 1)
    (s t : Bootstrapping.Term V ℒₛₑₜ) :
    T.internalize V ⊢ eqAtom s t 🡒 K.subst ![s] 🡒 K.subst ![t] :=
  setReplace T K s t

example (K : Bootstrapping.Semiformula V ℒₛₑₜ 1)
    (s t : Bootstrapping.Term V ℒₛₑₜ) :
    (𝗭𝗙 : SetTheory).internalize V ⊢ eqAtom s t 🡒 K.subst ![s] 🡒 K.subst ![t] :=
  setReplace (𝗭𝗙 : SetTheory) K s t

example (K : Bootstrapping.Semiformula V ℒₛₑₜ 1)
    (s t : Bootstrapping.Term V ℒₛₑₜ) :
    (𝗭𝗙𝗖 : SetTheory).internalize V ⊢ eqAtom s t 🡒 K.subst ![s] 🡒 K.subst ![t] :=
  setReplace (𝗭𝗙𝗖 : SetTheory) K s t

example (T : SetTheory) [T.Δ₁] [𝗘𝗤 ℒₛₑₜ ⪯ T]
    (K : Bootstrapping.Semiformula V ℒₛₑₜ 2) :
    T.internalize V ⊢ congruenceFormula 2 K := congruenceProof₂ T K

example (K : Bootstrapping.Semiformula V ℒₛₑₜ 2) :
    (𝗭𝗙 : SetTheory).internalize V ⊢ congruenceFormula 2 K :=
  congruenceProof₂ (𝗭𝗙 : SetTheory) K

example (K : Bootstrapping.Semiformula V ℒₛₑₜ 2) :
    (𝗭𝗙𝗖 : SetTheory).internalize V ⊢ congruenceFormula 2 K :=
  congruenceProof₂ (𝗭𝗙𝗖 : SetTheory) K

example (K : Bootstrapping.Semiformula V ℒₛₑₜ 2) :
    (𝗭𝗙 : SetTheory).internalize V ⊢ congruenceFormula 2 K.shift :=
  congruenceProof₂ (𝗭𝗙 : SetTheory) K.shift

example (x : V) :
    (𝗭𝗙 : SetTheory).internalize V ⊢ congruenceFormula 2
      (eqAtom (Bootstrapping.Semiterm.fvar x) (Bootstrapping.Semiterm.bvar 0)) :=
  congruenceProof₂ (𝗭𝗙 : SetTheory) _

example (K : Bootstrapping.Semiformula V ℒₛₑₜ 3) :
    (𝗭𝗙 : SetTheory).internalize V ⊢ congruenceFormula 3 K :=
  congruenceProof₃ (𝗭𝗙 : SetTheory) K

example (K : Bootstrapping.Semiformula V ℒₛₑₜ 1) :
    (𝗭𝗙 : SetTheory).internalize V ⊢ congruenceFormula 1 K :=
  congruenceProof₁ (𝗭𝗙 : SetTheory) K

example (K : Bootstrapping.Semiformula V ℒₛₑₜ 0) :
    (𝗭𝗙 : SetTheory).internalize V ⊢ congruenceFormula 0 K :=
  congruenceProof₀ (𝗭𝗙 : SetTheory) K

example {k : Nat} {arities : Fin k → Nat}
    (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i)) (i : Fin k) :
    translateFormula Ks
        (Rewriting.emb (setPlaceholderCongruenceSentence k arities i) :
          Proposition (setTemplateLanguage k arities)) =
      congruenceFormula (arities i) (Ks i) :=
  translate_setPlaceholderCongruenceSentence Ks i

example (K : Bootstrapping.Semiformula V ℒₛₑₜ 2) :
    translateFormula (fun _ : Fin 1 => K)
        (Rewriting.emb (setPlaceholderCongruenceSentence 1 (fun _ => 2) 0) :
          Proposition (setTemplateLanguage 1 (fun _ => 2))) =
      congruenceFormula 2 K :=
  translate_setPlaceholderCongruenceSentence (fun _ : Fin 1 => K) 0

example (K : Bootstrapping.Semiformula V ℒₛₑₜ 2) :
    (𝗭𝗙 : SetTheory).internalize V ⊢
      translateFormula (fun _ : Fin 1 => K)
        (Rewriting.emb (setPlaceholderCongruence 1 (fun _ => 2)) :
          Proposition (setTemplateLanguage 1 (fun _ => 2))) :=
  translatedCongruenceProof (𝗭𝗙 : SetTheory) (fun _ : Fin 1 => K)
    (fun _ => congruenceProof₂ (𝗭𝗙 : SetTheory) K)
