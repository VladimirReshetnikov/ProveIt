import DiophantineConsistency.ArithmeticAdaptiveConstructionTransportPositive2011

/-! Bind transport positivity to the actual fourteen-coordinate equations. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveConstructionTransportActual2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCarrierSoundness2011 ArithmeticCarrierRadix2011
  ArithmeticAdaptiveConstructionTransport2011 ArithmeticAdaptiveConstructionTransportPositive2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The actual equations and the three rank/radix facts present in the
Assembly imply the nonzero transport quotient needed by the first carrier. -/
theorem actual_transport_quotient_positive (v : Fin 14 → V) (u : V)
    (hv : ∀ j, 0<v j)
    (he : Equations (CurrentMasks2011.beta:V) (CurrentKernel2011.K:V)
      (CurrentMasks2011.lowPort:V) ((CurrentMasks2011.highPort+CurrentMasks2011.beta:ℕ):V) v)
    (hq : ArithmeticCarrierRadix2011.q v=Exp.exp u)
    (hX : Exp.exp (rank v)=ArithmeticCarrierRadix2011.q v*v 8)
    (hR : 2*u≤rank v) : 1≤ArithmeticCarrierRadix2011.q v*(v 3-1) := by
  let q := ArithmeticCarrierRadix2011.q v
  let C := q-v 1-v 2
  have hqpos : 0<q := by
    change 0<ArithmeticCarrierRadix2011.q v
    rw [hq]
    exact exp_pos _
  have ht := adaptive_transport_of_equations v hv he
  change 0<C ∧ (q*(CurrentKernel2011.K:V)+q*v 8)*C =
    q*v 1+(q-1)*(q*(v 3-1)) at ht
  have hF : v 1<q := by
    have hc1 : 0<q-v 1 := lt_of_lt_of_le ht.1 tsub_le_self
    exact tsub_pos_iff_lt.mp hc1
  have hw : q≤v 8 := radix_le_multiplier u (rank v) q (v 8) hq hX hR
  have htrans : ((CurrentKernel2011.K:V)+v 8)*C=v 1+(v 3-1)*(q-1) := by
    apply mul_left_cancel₀ (ne_of_gt hqpos)
    calc q*(((CurrentKernel2011.K:V)+v 8)*C) =
        (q*(CurrentKernel2011.K:V)+q*v 8)*C := by ring
      _ = q*v 1+(q-1)*(q*(v 3-1)) := ht.2
      _ = q*(v 1+(v 3-1)*(q-1)) := by ring
  exact transport_quotient_positive q (CurrentKernel2011.K:V) (v 8) C (v 1) (v 3)
    hqpos ht.1 hw hF htrans
end DiophantineConsistency.ArithmeticAdaptiveConstructionTransportActual2011
