import ZFCinPA.ModelCodedTwoQuantifierSwap

set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.ZFCinPA.ModelCodedBindOneSwap
open LeanProofs.ZFCinPA.ModelCodedTwoQuantifierSwap
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]
#print axioms LeanProofs.ZFCinPA.ModelCodedTwoQuantifierSwap.generalizeTwo
#print axioms LeanProofs.ZFCinPA.ModelCodedTwoQuantifierSwap.allSwap
#print axioms LeanProofs.ZFCinPA.ModelCodedTwoQuantifierSwap.typed_swap_val
example (T : InternalTheory V L) (p : Bootstrapping.Semiformula V L 2) :
    T ⊢! (∀⁰ ∀⁰ p) 🡒 (∀⁰ ∀⁰ (p.subst ![Semiterm.bvar 1,Semiterm.bvar 0])) := allSwap T p
example (T : InternalTheory V L) (p : Bootstrapping.Semiformula V L 2) :
    T ⊢ (∀⁰ ∀⁰ p) 🡒 (∀⁰ ∀⁰ (p.subst ![Semiterm.bvar 1,Semiterm.bvar 0])) := ⟨allSwap T p⟩
example (p : Bootstrapping.Semiformula V L 2) :
    (p.subst (![Semiterm.bvar 1,Semiterm.bvar 0] : SemitermVec V L 2 2)).val = subst L (swapVec L (0 : V)) p.val :=
  typed_swap_val p
example (T : InternalTheory V L) (Γ : List (Formula V L))
    (p : Bootstrapping.Semiformula V L 2)
    (d : Γ.map (fun r => r.shift.shift) ⊢[T]!
      p.shift.shift.subst ![Semiterm.fvar 0,Semiterm.fvar 1]) :
    Γ ⊢[T]! ∀⁰ ∀⁰ p := generalizeTwo T d
