import ZFCinPA.OpenTemplateClosure

set_option autoImplicit false
noncomputable section

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.ZFCinPA.SetPlaceholders
open LeanProofs.ZFCinPA.OpenSetTemplateCompiler
open LeanProofs.ZFCinPA.OpenTemplateClosure
open scoped LO.FirstOrder.Arithmetic

#print axioms LeanProofs.ZFCinPA.OpenTemplateClosure.shifts_all
#print axioms LeanProofs.ZFCinPA.OpenTemplateClosure.generalizeAll
#print axioms LeanProofs.ZFCinPA.OpenTemplateClosure.translate_closed_shifts
#print axioms LeanProofs.ZFCinPA.OpenTemplateClosure.closeTemplate

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

example (T : InternalTheory V L) {n : Nat} (p : Semiformula V L n)
    (h : T ⊢! (shifts n p).subst (freshTuple n)) : T ⊢! ∀⁰* p :=
  generalizeAll T p h

example (T : InternalTheory V L) (p : Semiformula V L 2)
    (h : T ⊢! p.shift.shift.subst (freshTuple 2)) : T ⊢! ∀⁰ ∀⁰ p :=
  generalizeAll T p h

example {k : Nat} {a : Fin k → Nat}
    (Ks : (i : Fin k) → Semiformula V ℒₛₑₜ (a i))
    (T : InternalTheory V ℒₛₑₜ) (p : Proposition (setTemplateLanguage k a))
    (h : ∀ b, T ⊢! translateFormula (shiftedPredicates Ks b) p) :
    T ⊢! translateFormula Ks (Rewriting.emb p.univCl) := closeTemplate Ks T p h

example (K : Semiformula V ℒₛₑₜ 2) (T : InternalTheory V ℒₛₑₜ)
    (p : Proposition (setTemplateLanguage 1 (fun _ => 2)))
    (h : ∀ b, T ⊢! translateFormula (shiftedPredicates (fun _ => K) b) p) :
    T ⊢! translateFormula (fun _ => K) (Rewriting.emb p.univCl) :=
  closeTemplate (fun _ => K) T p h
