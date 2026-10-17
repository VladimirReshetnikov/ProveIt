import ZFCinPA.ModelCodedNamedQuantifierTemplates254

set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.ZFCinPA.ModelCodedNamedQuantifierTemplates254
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]
#print axioms LeanProofs.ZFCinPA.ModelCodedNamedQuantifierTemplates254.allDistribution
example (T : InternalTheory V L) (p q : Semiformula V L 1) :
    T ⊢! (∀⁰ (p 🡒 q)) 🡒 ((∀⁰ p) 🡒 (∀⁰ q)) := allDistribution T p q
example (T : InternalTheory V L) (p q : Semiformula V L 1) :
    T ⊢ (∀⁰ (p 🡒 q)) 🡒 ((∀⁰ p) 🡒 (∀⁰ q)) := ⟨allDistribution T p q⟩
example (T : InternalTheory V L) (p : Semiformula V L 1) :
    T ⊢! (∀⁰ (p 🡒 p)) 🡒 ((∀⁰ p) 🡒 (∀⁰ p)) := allDistribution T p p
