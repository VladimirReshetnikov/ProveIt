import Model69FreshNorms

/-! Experimental abstract four-slot specialization. It avoids normalizing the
large fixed port values while applying the symbolic-port converse. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Model69ExactPort
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 ObjectCurrentEquation2011

/-- Build the port vector once with abstract entries, before instantiating
large current-2011 coefficients. -/
theorem four_slots {V : Type*} (B K L M : V) :
    ∃ p : Fin 4 → V, p 0=B ∧ p 1=K ∧ p 2=L ∧ p 3=M := by
  exact ⟨![B,K,L,M],rfl,rfl,rfl,rfl⟩

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.radix CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort

/-- Actual positive current-2011 zeros give zeros of the exact shifted
69-node 2011 literal, with no supplied port-vector hypothesis. -/
theorem current_shifted_zero_exact (v : Fin 14 → V)
    (hv : ∀ j, 0<v j)
    (hz : expression.splitNatural.1.evalSemiring v=expression.splitNatural.2.evalSemiring v) :
    ∃ u : Fin 13 → V, InternalZero Thirteen69Cuts.currentLiteral u := by
  obtain ⟨p,h0,h1,h2,h3⟩ := four_slots (CurrentMasks2011.beta:V)
    (CurrentKernel2011.K:V) (CurrentMasks2011.lowPort:V)
    ((CurrentMasks2011.highPort+CurrentMasks2011.beta:ℕ):V)
  exact Model69FreshNorms.current_shifted_zero p v h0 h1 h2 h3 hv hz
end Model69ExactPort
#print axioms Model69ExactPort.four_slots
#print axioms Model69ExactPort.current_shifted_zero_exact
