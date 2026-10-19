import ZFCinPA.NativeGicDelta1

set_option autoImplicit false
noncomputable section

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.ZFCinPA

#print axioms LeanProofs.ZFCinPA.gicBody_quote
#print axioms LeanProofs.ZFCinPA.gicBodyVal_eq
#print axioms LeanProofs.ZFCinPA.gicBodyVal_quote
#print axioms LeanProofs.ZFCinPA.le_gicBodyVal_quote
#print axioms LeanProofs.ZFCinPA.gicBodyVal.defined
#print axioms LeanProofs.ZFCinPA.GicR.defined
#print axioms LeanProofs.ZFCinPA.gicTheory_delta1

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (ψ : SetTheorySemiproposition 2) :
    (⌜gicBodyMeta ψ⌝ : Bootstrapping.Semiformula V ℒₛₑₜ 0) = gicBody ⌜ψ⌝ :=
  gicBody_quote ψ

example (K : Bootstrapping.Semiformula V ℒₛₑₜ 2) :
    gicBodyVal K.val = (gicBody K).val := gicBodyVal_eq K

example (ψ : SetTheorySemiproposition 2) :
    gicBodyVal (⌜ψ⌝ : ℕ) = (⌜gicBodyMeta ψ⌝ : ℕ) := gicBodyVal_quote ψ

example (k : V) :
    Bootstrapping.subst ℒₛₑₜ ((gicSubst01Const : ℕ) : V) k ≤ gicBodyVal k :=
  subst01_le_gicBodyVal k

example (ψ : SetTheorySemiproposition 2) :
    (⌜ψ⌝ : ℕ) ≤ gicBodyVal (⌜ψ⌝ : ℕ) := le_gicBodyVal_quote ψ

example : 𝚺₁-Function₁ (gicBodyVal : V → V) via gicBodyValGraph :=
  gicBodyVal.defined

example : 𝚫₁-Predicate[V] (GicR : V → Prop) via gicCh := GicR.defined

example (p : V) : GicR p ↔ SchemaRecognizer ℒₛₑₜ 2 gicBodyVal p := Iff.rfl

example : gicTheory.Δ₁ := gicTheory_delta1

example (ψ : SetTheorySemiproposition 2) :
    FirstOrder.Semiformula.univCl (gicBodyMeta ψ) ∈ gicTheory := ⟨ψ, rfl⟩
