import ZFCinPA.ModelCodedNamedBinderLaws

set_option autoImplicit false

/-!
Finite internal universal-distribution proof for arbitrary internal typed
matrices. This is a logical template; numerical rho2 and its zero implication
alias are separate clients. No theory axioms or matrix support premise is used.
-/
namespace LeanProofs.ZFCinPA.ModelCodedNamedQuantifierTemplates254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LO.Entailment
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

noncomputable def allDistribution (T : InternalTheory V L)
    (p q : Semiformula V L 1) :
    T ⊢! (∀⁰ (p 🡒 q)) 🡒 ((∀⁰ p) 🡒 (∀⁰ q)) := by
  apply FiniteContext.deduct'
  apply TProof.allImpAll
  have h : [(∀⁰ (p 🡒 q)).shift] ⊢[T]! ∀⁰ (p 🡒 q).shift := by
    simpa using (FiniteContext.byAxm₀ (𝓢 := T) (Γ := [])
      (φ := (∀⁰ (p 🡒 q)).shift))
  simpa [Bootstrapping.Semiformula.free] using
    (TProof.specializeWithCtx h (Semiterm.fvar (0 : V)))

end LeanProofs.ZFCinPA.ModelCodedNamedQuantifierTemplates254
