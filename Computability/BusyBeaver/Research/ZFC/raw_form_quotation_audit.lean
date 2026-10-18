import ZFCinPA.RawFormQuotation

set_option autoImplicit false
noncomputable section

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.ZFCinPA.RawFormQuotation
open scoped LO.FirstOrder.Arithmetic

#print axioms LeanProofs.ZFCinPA.RawFormQuotation.shift_quote_sen
#print axioms LeanProofs.ZFCinPA.RawFormQuotation.isSemiformula_quote_sen
#print axioms LeanProofs.ZFCinPA.RawFormQuotation.quote_closed
#print axioms LeanProofs.ZFCinPA.RawFormQuotation.isSemiformula_closed
#print axioms LeanProofs.ZFCinPA.RawFormQuotation.shift_closed

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example {k : Nat} (σ : Semisentence ℒₛₑₜ k) :
    shift ℒₛₑₜ (⌜σ⌝ : V) = ⌜σ⌝ := shift_quote_sen σ

example {k : Nat} (σ : Semisentence ℒₛₑₜ k) :
    IsSemiformula ℒₛₑₜ (k : V) (⌜σ⌝ : V) := isSemiformula_quote_sen σ

example (k : Nat) (φ : _root_.SetTheory.Form) :
    closed k φ = closeS (translate (k + 1) φ) := rfl

example (k : Nat) (φ : _root_.SetTheory.Form) :
    (⌜closed k φ⌝ : V) =
      ⌜(Rewriting.emb (closeS (translate (k + 1) φ)) : SetTheorySemiproposition (k + 1))⌝ :=
  quote_closed k φ

example (k : Nat) (φ : _root_.SetTheory.Form) :
    IsSemiformula ℒₛₑₜ ((k + 1 : Nat) : V) (⌜closed k φ⌝ : V) :=
  isSemiformula_closed k φ

example (k : Nat) (φ : _root_.SetTheory.Form) :
    shift ℒₛₑₜ (⌜closed k φ⌝ : V) = ⌜closed k φ⌝ := shift_closed k φ

example (φ : _root_.SetTheory.Form) :
    IsSemiformula ℒₛₑₜ 1 (⌜closed 0 φ⌝ : V) := by
  simpa using isSemiformula_closed (V := V) 0 φ

example (φ : _root_.SetTheory.Form) :
    IsSemiformula ℒₛₑₜ 2 (⌜closed 1 φ⌝ : V) := by
  simpa using isSemiformula_closed (V := V) 1 φ
