import DiophantineConsistency.ArithmeticAdaptiveConstructionConditionalExists2011
import DiophantineConsistency.AdaptiveFirstRootFactor87Literal

/-! Transfer the conditional construction to the 87-gate output. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveConstructionReduced2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticCarrierSoundness2011 ArithmeticCarrierRadix2011
  ArithmeticPellRecurrence ArithmeticOuterSeed ArithmeticAdaptiveConstructionConditionalExists2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The exact enriched Assembly conclusion conditionally gives a zero of the
87-gate adaptive output at the maintained ports. -/
theorem reduced_zero_of_enriched_assembly (B : V)
    (hassembly : ∃ v : Fin 14 → V, (∀ j, 0<v j) ∧
      v 1≤(CurrentMasks2011.beta:V)*v 0+1 ∧
      Equations (CurrentMasks2011.beta:V) (CurrentKernel2011.K:V)
        (CurrentMasks2011.lowPort:V) ((CurrentMasks2011.highPort+CurrentMasks2011.beta:ℕ):V) v ∧
      (∀ j, v j≤B) ∧ rank v%4=3 ∧ (∃ b, v 12=ycoord (rank v) b) ∧
      ∃ u, ArithmeticCarrierRadix2011.q v=Exp.exp u ∧
        Exp.exp (rank v)=ArithmeticCarrierRadix2011.q v*v 8 ∧ 2*u≤rank v ∧
        SeedRelations u (rank v) (v 7) (v 9) (v 10) (v 11) (v 13) ∧
        let q := ArithmeticCarrierRadix2011.q v
        let Y := v 7*q^3
        let c := (v 10+v 11)*Y+v 10
        let L := v 4*v 4*c*v 6
        let M := v 4*v 4*rank v+c
        L=(L-M)+(M-L)+c+v 4*v 4*rank v) :
    ∃ x : Fin 13 → V, InternalZero AdaptiveFirstRootFactor87Literal.naturalExpression87 x := by
  obtain ⟨x,hx⟩ := shifted_zero_of_enriched_assembly B hassembly
  exact ⟨x,(AdaptiveFirstRootFactor87Literal.current_natural_zero_iff x).mp hx⟩
end DiophantineConsistency.ArithmeticAdaptiveConstructionReduced2011
