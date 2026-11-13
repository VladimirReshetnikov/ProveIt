import Trace74PellCarrierInternal
import Trace74CRTNaturalTuple

/-! Bind the internal Pell carrier factor to the actual chart parameters. -/
set_option autoImplicit false
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace Trace74PellCarrierGraph
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing ArithmeticPellRecurrence ArithmeticPow
open Trace74PellCarrierInternal
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The actual graph `H ∣ K` premise follows when the chart's three
natural parameters are the indicated internal Pell quantities. -/
theorem graph_carrier_factor (p : Fin 4 → V) (v : Fin 10 → V) (b n : V)
    (hx : let q := p 0*v 0+1; v 5*q=power 2 n)
    (hc : let q := p 0*v 0+1; let Y := (q*q*q)*v 6;
      (v 8+v 9)*Y+v 8=ycoord n b)
    (ha : let q := p 0*v 0+1; let X := v 5*q; let Y := (q*q*q)*v 6;
      X*Y+Y=b+1) :
    let P := fun i => (ι (p i) : DiffRing V)
    let V₀ := fun i => (ι (v i) : DiffRing V)
    let q := P 0*V₀ 0+1
    let X := V₀ 5*q
    let Y := (q*q*q)*V₀ 6
    let c := (V₀ 8+V₀ 9)*Y+V₀ 8
    let H := 4*(X*Y+Y)-1
    H ∣ X*(3*c-2*X)+2 := by
  have hX := congrArg ι hx
  have hC := congrArg ι hc
  have hA := congrArg ι ha
  simp only [map_add,map_mul,map_one] at hX hC hA
  dsimp only
  rw [hA,hX,hC]
  convert carrier_factor b n using 1 <;> ring

#print axioms Trace74PellCarrierGraph.graph_carrier_factor
end Trace74PellCarrierGraph
