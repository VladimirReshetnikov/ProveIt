import Trace74SymbolicCoverModel
import Trace74SaturationMaskGuard
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74FixedMaskSaturationGuard
open CompactFixedBeta CompactSymbolicPorts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticBinaryPopulation ArithmeticBinaryCarry
open ArithmeticSaturation Trace74SaturationMaskGuard
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Discharge only fixed symbolic mask coverage; other saturation premises remain explicit. -/
theorem guard (u q J F C R : V)
    (hq : q = Exp.exp u) (hqdef : q = (betaNat:V)*J+1)
    (hJ : 0<J) (hHPJ : 1≤(highNat:V)*J) (hHP : (highNat:V)≤(betaNat:V))
    (hC : 0<C) (hA : C-1<q) (hF : F<q) (hM : (lowNat:V)*J+1<q)
    (hblock : R=(C-1)+((lowNat:V)*J+1)+q*(F+((highNat:V)*J-1))+
      q^2*(q-1-(C-1))+q^3*(q-1-F))
    (hpopulation : population ((lowNat:V)*J+1)+population ((highNat:V)*J-1)≤u+2)
    (hrank : 3*u+2≤population R) :
    NoCarry (C-1) ((lowNat:V)*J+1) ∧ NoCarry F ((highNat:V)*J-1) ∧ F+C<q := by
  exact guard_from_saturation_and_cover u q (betaNat:V) (lowNat:V) (highNat:V) J F C R
    hq hqdef hJ hHPJ (Trace74SymbolicCoverModel.cover_model (V:=V)) hHP
    hC hA hF hM hblock hpopulation hrank

#print axioms Trace74FixedMaskSaturationGuard.guard
end Trace74FixedMaskSaturationGuard
