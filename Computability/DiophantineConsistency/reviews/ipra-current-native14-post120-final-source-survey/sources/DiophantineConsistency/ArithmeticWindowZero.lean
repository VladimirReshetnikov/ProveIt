import DiophantineConsistency.ArithmeticWindowInterface
import DiophantineConsistency.ArithmeticHalfBinomial2011
import DiophantineConsistency.ArithmeticCurrentSentence2011

/-! The internal window of a positive zero of the literal current polynomial, in
every model of IΣ1, with the population lower bound discharged by the internal
half-binomial argument (`ArithmeticHalfBinomial2011.current_population_lower`). -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticWindowZero
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticBinaryPopulation ArithmeticWindowInterface ArithmeticCurrentSentence2011
  ArithmeticCarrierSoundness2011 ArithmeticCarrierRadix2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.radix CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- **The window of a positive zero**, at the radix block count. -/
theorem window_of_positive_zero (u : Fin 14 → V) (h : PositiveZero u) :
    ∃ N : V, q u = Exp.exp (94517*N) ∧
      Window N (rank u - 94517*N) (q u - u 1 - u 2) (u 1) := by
  refine window_of_equations u h.1 (current_equations u h.1 h.2) (current_radix u h.1 h.2).2 ?_
  intro N hqN
  obtain ⟨L, _, hqL, _, _, _, _, hpop⟩ :=
    ArithmeticHalfBinomial2011.current_population_lower u h.1 h.2
  rw [(current_width (V:=V)).1] at hqL hpop
  have hLN : (94517:V)*L = 94517*N := exp_inj (hqL.symm.trans hqN)
  rw [← hLN]
  exact hpop

/-- **The window of a positive zero** (existential form). -/
theorem window_of_zero (u : Fin 14 → V) (h : PositiveZero u) :
    ∃ N W C F : V, Window N W C F := by
  obtain ⟨N, -, hw⟩ := window_of_positive_zero u h
  exact ⟨N, _, _, _, hw⟩

end DiophantineConsistency.ArithmeticWindowZero
