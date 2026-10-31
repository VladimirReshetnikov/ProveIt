import DiophantineConsistency.AdaptiveGap85FixedPortBounds
import DiophantineConsistency.AdaptiveGap85ActualPortBound

/-! Conditional digit bounds at the fixed 85-equation ports. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85FixedPortClient
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticPellRecurrence ArithmeticPellHalfIndex
open ArithmeticAdaptiveScaledNorms2011 AdaptiveGap85Literal AdaptiveGap85ActualPortBound
open AdaptiveGap85FixedPortBounds
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.radix CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Fixed ports and an actual shifted zero discharge the port/positivity
premises; the signed-rank smallness premise remains explicit. -/
theorem fixed_shifted_port_bounds85 (v : Fin 13 → V) (n : V)
    (hz : InternalZero (positiveShift (expressionAt85 (fun j => (currentPorts j:ℤ)))) v)
    (hn : 0<n)
    (hny : let w := fun j : Fin 13 => v j+1
      2*ycoord n (2*((w 6*w 7)*w 7-1)+1)=w 9+w 10)
    (hsmall : let w := fun j : Fin 13 => v j+1
      let q : V := 1+w 0*(currentPorts 0:V)
      let q2 : V := q*q
      let neg : V := q*w 1+w 2
      let rp : V := q2*q2+neg+w 0*((currentPorts 2:V)+(currentPorts 3:V)*q)
      let rn : V := q2+neg*q2
      absdiff rp rn+2*n<q^4) :
    let w := fun j : Fin 13 => v j+1
    let q : V := 1+w 0*(currentPorts 0:V)
    q*w 1+w 2<q*q+2 ∧ w 1≤q ∧ (w 1=q → w 2=1) := by
  obtain ⟨hb,hMC,hMF⟩ := fixed_port_bounds85 (V:=V)
  have hv : ∀j : Fin 13,0<(v j+1) := fun j => lt_of_le_of_lt (Arithmetic.zero_le (v j)) (lt_add_one _)
  have hz' : InternalZero (expressionAt85 (fun j => (currentPorts j:ℤ))) (fun j => v j+1) :=
    (internalZero_positiveShift _ _).mp hz
  exact expressionAt_port_bounds85 currentPorts (fun j => v j+1) n hb hv hMC hMF hz' hn hny hsmall
end DiophantineConsistency.AdaptiveGap85FixedPortClient
