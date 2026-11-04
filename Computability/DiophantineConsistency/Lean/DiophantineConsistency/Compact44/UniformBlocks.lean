import DiophantineConsistency.Compact44.CompactCellDigitUniform
import DiophantineConsistency.ArithmeticPackingBlocks

/-! Uniform model-definability of packed blocks with two varying parameters. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace UniformBlocks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticWindowDigits
open DiophantineConsistency.ArithmeticPackingBlocks

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A uniformly definable, uniformly bounded digit family yields a uniformly
    definable block sum in its two parameters. -/
theorem bsum_uniform (f : V → V → V → V) [𝚺₁-Function₃ f] (w n : V)
    (hf : ∀ a b j, f a b j < Exp.exp w) :
    𝚺₁-Function₂ (fun a b => bsum w (f a b) n) := by
  have hR : 𝚺₁.Definable (fun v : Fin 3 → V =>
      v 0 < Exp.exp (w * n) ∧ ∀ j < n, dig w (v 0) j = f (v 1) (v 2) j) := by
    definability
  apply hR.of_iff
  intro v
  letI : 𝚺₁-Function₁ (f (v 1) (v 2)) := by definability
  exact bsum_graph (fun j _ => hf (v 1) (v 2) j) (v 0)

#print axioms UniformBlocks.bsum_uniform
end UniformBlocks
