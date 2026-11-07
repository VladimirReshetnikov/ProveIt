import DiophantineConsistency.Sign28CurrentConsIff

/-! Uncompiled transport with an arbitrary target proposition. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign28AbstractTarget
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
  SharingSeed28Sextic.seed SharingSeed31Sextic.seed CurrentWindowCarry2011.ports

theorem transfer (T : Prop)
    (h : (∃ w : Fin 31 → V, InternalZero (SharingSeed31Sextic.seed CurrentWindowCarry2011.ports) (Fin.cons (1 : V) w)) ↔ T) :
    (∃ w : Fin 28 → V, InternalZero (SharingSeed28Sextic.seed CurrentWindowCarry2011.ports) (Fin.cons (1 : V) w)) ↔ T :=
  Iff.trans (Sign28CurrentConsIff.seed_cons_iff (V := V)) h
end DiophantineConsistency.Sign28AbstractTarget
#print axioms DiophantineConsistency.Sign28AbstractTarget.transfer
