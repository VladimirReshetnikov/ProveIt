import DiophantineConsistency.Adm942.Adm942WindowInterface
import DiophantineConsistency.Adm942.Adm942HalfBinomial

/-! # The window of a positive admissible942 zero

The counterpart of `ArithmeticWindowZero`: in every model of IΣ1, a positive
zero of the literal Carrier65 expression at the admissible942 ports
(`Adm942Ports.PositiveZero`) gives the admissible942 window, with the
population lower bound discharged by the internal half-binomial argument
(`Adm942HalfBinomial.current_population_lower`). -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Adm942WindowZero
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticBinaryPopulation Adm942WindowInterface Adm942Ports Adm942CarrierRadix
attribute [local irreducible] Adm942Kernel.K Adm942MaskData.radix Adm942MaskData.beta
  Adm942MaskData.lowPort Adm942MaskData.highPort
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- **The window of a positive zero**, at the radix block count. -/
theorem window_of_positive_zero (u : Fin 14 → V) (h : PositiveZero u) :
    ∃ N : V, q u = Exp.exp (189269*N) ∧
      Window N (rank u - 189269*N) (q u - u 1 - u 2) (u 1) := by
  refine window_of_equations u h.1 (current_equations u h.1 h.2) (current_radix u h.1 h.2).2 ?_
  intro N hqN
  obtain ⟨L, _, hqL, _, _, _, _, hpop⟩ :=
    Adm942HalfBinomial.current_population_lower u h.1 h.2
  rw [(current_width (V:=V)).1] at hqL hpop
  have hLN : (189269:V)*L = 189269*N := exp_inj (hqL.symm.trans hqN)
  rw [← hLN]
  exact hpop

/-- **The window of a positive zero** (existential form). -/
theorem window_of_zero (u : Fin 14 → V) (h : PositiveZero u) :
    ∃ N W C F : V, Window N W C F := by
  obtain ⟨N, -, hw⟩ := window_of_positive_zero u h
  exact ⟨N, _, _, _, hw⟩

/-- The window of a natural zero (the maintained single positive shift). -/
theorem window_of_natural_zero (v : Fin 14 → V)
    (hz : naturalExpression.splitNatural.1.evalSemiring v =
      naturalExpression.splitNatural.2.evalSemiring v) :
    ∃ N : V, q (fun j => v j + 1) = Exp.exp (189269*N) ∧
      Window N (rank (fun j => v j + 1) - 189269*N)
        (q (fun j => v j + 1) - (v 1 + 1) - (v 2 + 1)) (v 1 + 1) :=
  window_of_positive_zero _
    ⟨fun j => lt_of_le_of_lt (Arithmetic.zero_le (v j)) (lt_add_one _), (natural_zero_iff v).mp hz⟩

end Adm942WindowZero

#print axioms Adm942WindowZero.window_of_positive_zero
#print axioms Adm942WindowZero.window_of_zero
#print axioms Adm942WindowZero.window_of_natural_zero
