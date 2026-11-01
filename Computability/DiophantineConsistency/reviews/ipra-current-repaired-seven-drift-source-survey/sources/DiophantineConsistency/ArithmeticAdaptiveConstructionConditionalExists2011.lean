import DiophantineConsistency.ArithmeticAdaptiveConstructionConditional2011

/-! The exact strengthened Assembly conclusion implies a conditional zero. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveConstructionConditionalExists2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticCarrierSoundness2011 ArithmeticCarrierRadix2011
  ArithmeticPellRecurrence ArithmeticOuterSeed ArithmeticAdaptiveConstructionConditional2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The exact strengthened Assembly conclusion, with an arbitrary preserved
bound, implies the shifted literal zero without importing Assembly. -/
theorem shifted_zero_of_enriched_assembly (B : V)
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
    ∃ x : Fin 13 → V, InternalZero naturalExpression x := by
  obtain ⟨v,hv,hF,he,_,hphase,⟨b,hy⟩,u,hq,hX,hR,hseed,horient⟩ := hassembly
  apply shifted_zero_of_enriched_witness v u b hv
  · change v 1≤(CurrentMasks2011.beta:V)*v 0+1
    exact hF
  · exact he
  · exact hphase
  · exact hy
  · exact hq
  · exact hX
  · exact hR
  · exact hseed
  · exact horient
end DiophantineConsistency.ArithmeticAdaptiveConstructionConditionalExists2011
