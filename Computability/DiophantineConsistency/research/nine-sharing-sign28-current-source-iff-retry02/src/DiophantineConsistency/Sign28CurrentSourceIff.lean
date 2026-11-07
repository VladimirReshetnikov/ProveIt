import DiophantineConsistency.Sign28CurrentConsIff
import DiophantineConsistency.Sign31CurrentSourceIff

/-! Uncompiled explicit iff-transitivity retry; final statement unchanged. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign28CurrentSourceIff
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
  SharingSeed28Sextic.seed SharingSeed31Sextic.seed CurrentWindowCarry2011.ports
  ObjectCurrentEquation2011.naturalExpression

theorem seed_exists_iff_source :
    (∃ w : Fin 28 → V, InternalZero (SharingSeed28Sextic.seed CurrentWindowCarry2011.ports) (Fin.cons (1 : V) w)) ↔
      ∃ u : Fin 14 → V, ObjectCurrentEquation2011.InternalZero ObjectCurrentEquation2011.naturalExpression u := by
  exact Iff.trans (Sign28CurrentConsIff.seed_cons_iff (V := V))
    (Sign31CurrentSourceIff.seed_exists_iff_source (V := V))
end DiophantineConsistency.Sign28CurrentSourceIff
#print axioms DiophantineConsistency.Sign28CurrentSourceIff.seed_exists_iff_source
