import DiophantineConsistency.ArithmeticAdaptiveConstructionAux2011

/-! Bind reverse auxiliary positivity to the maintained equation coordinates. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveConstructionAuxClient2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCarrierSoundness2011 ArithmeticCarrierRadix2011 ArithmeticAdaptiveConstructionAux2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The actual auxiliary norm supplies the positive adaptive coordinate when
its ordinate is at least two. The bound remains explicit. -/
theorem adaptive_auxiliary_of_equations (v : Fin 14 → V)
    (he : Equations (CurrentMasks2011.beta:V) (CurrentKernel2011.K:V)
      (CurrentMasks2011.lowPort:V) ((CurrentMasks2011.highPort+CurrentMasks2011.beta:ℕ):V) v)
    (hy : 2≤v 12) :
    let q := ArithmeticCarrierRadix2011.q v
    let X := v 8*q
    let Y := v 7*q^3
    let a := X*Y+Y
    let c := (v 10+v 11)*Y+v 10
    let delta := (a+1)*(a+3)
    let R := ArithmeticCarrierRadix2011.rank v
    let Vabs := (v 4*v 4*c*v 6-(v 4*v 4*R+c))+((v 4*v 4*R+c)-v 4*v 4*c*v 6)
    0<v 12-Vabs ∧ (v 12-Vabs)+Vabs=v 12 ∧
      (delta*v 5*c*c)*(delta*v 5*c*c)*Vabs*Vabs+v 12*v 12 =
        1+(delta*v 5*c*c)*(delta*v 5*c*c)*v 12*v 12 := by
  dsimp only
  have h := he.2.2.2.2
  refine ⟨?_,?_,h⟩
  · exact (positive_auxiliary_witness _ _ _ hy h).1
  · exact (positive_auxiliary_witness _ _ _ hy h).2
end DiophantineConsistency.ArithmeticAdaptiveConstructionAuxClient2011
