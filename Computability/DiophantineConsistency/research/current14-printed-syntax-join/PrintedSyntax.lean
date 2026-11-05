import Current14LiteralPorts
import DiophantineConsistency.CurrentEquationSyntax2011

/-! A structured, printed-recipe version of the maintained literal syntax.
This is not a parser or semantics for TeX/PDF. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Current14PrintedSyntax
open DiophantineConsistency ObjectCurrentEquation2011

attribute [local irreducible] CurrentWindowCarry2011.ports CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
  Current14LiteralPorts.K Current14LiteralPorts.beta Current14LiteralPorts.mu
  Current14LiteralPorts.omega

/-- The printed rational formula for K is integral, so its floor is exactly K. -/
def ports : Fin 4 → ℤ :=
  ![Current14LiteralPorts.beta, ⌊Current14LiteralPorts.K⌋,
    Current14LiteralPorts.mu, Current14LiteralPorts.omega]

theorem kernel_floor : (CurrentKernel2011.K : ℤ) = ⌊Current14LiteralPorts.K⌋ := by
  rw [← Current14LiteralPorts.K_eq]
  exact (Int.floor_natCast CurrentKernel2011.K).symm

private theorem fin4_ext {α : Type*} (p q : Fin 4 → α)
    (h0 : p 0 = q 0) (h1 : p 1 = q 1)
    (h2 : p 2 = q 2) (h3 : p 3 = q 3) : p = q := by
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

theorem ports_eq : CurrentWindowCarry2011.ports = ports := by
  obtain ⟨h0, h1, h2, h3⟩ := Current14LiteralPorts.all_ports
  have h1int : CurrentWindowCarry2011.ports 1 = ⌊Current14LiteralPorts.K⌋ := by
    have h := congrArg Int.floor h1
    simpa only [Int.floor_intCast] using h
  exact fin4_ext _ _ h0 h1int h2 h3

theorem expression_eq : expression = expressionAt ports := by
  rw [expression, ports_eq]

theorem naturalExpression_eq :
    naturalExpression = positiveShift (expressionAt ports) := by
  rw [naturalExpression, expression_eq]

#print axioms kernel_floor
#print axioms ports_eq
#print axioms expression_eq
#print axioms naturalExpression_eq
end Current14PrintedSyntax
