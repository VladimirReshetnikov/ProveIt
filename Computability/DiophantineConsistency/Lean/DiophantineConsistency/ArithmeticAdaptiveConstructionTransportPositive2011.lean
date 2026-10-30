import DiophantineConsistency.ArithmeticAdaptiveConstructionTransport2011

/-! Prove that the old transport quotient used by the adaptive first carrier
is nonzero under the explicit rank-growth condition. -/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticAdaptiveConstructionTransportPositive2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The actual exponential multiplier is at least the radix when the rank is
at least twice the radix exponent. -/
theorem radix_le_multiplier (u R q w : V)
    (hq : q=Exp.exp u) (hX : Exp.exp R=q*w) (hR : 2*u≤R) : q≤w := by
  have hqpos : 0<q := by rw [hq]; exact exp_pos _
  have hsq : q*q≤q*w := by
    calc q*q = Exp.exp (u+u) := by rw [hq, exp_add]
         _ ≤ Exp.exp R := exp_monotone_le.mpr (by simpa only [two_mul] using hR)
         _ = q*w := hX
  exact le_of_mul_le_mul_left hsq hqpos

/-- A positive gap, a multiplier at least q, and F<q force the deleted
transport quotient to be positive. No standard-model argument is used. -/
theorem transport_quotient_positive (q K w C F z : V)
    (hq : 0<q) (hC : 0<C) (hw : q≤w) (hF : F<q)
    (ht : (K+w)*C=F+(z-1)*(q-1)) : 1≤q*(z-1) := by
  have hqA : q≤(K+w)*C := by
    calc q ≤ w := hw
         _ ≤ K+w := le_add_of_nonneg_left (Arithmetic.zero_le K)
         _ ≤ (K+w)*C := le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp hC)
  have hz : 1<z := by
    by_contra hn
    have hz0 : z-1=0 := tsub_eq_zero_of_le (le_of_not_gt hn)
    rw [hz0,zero_mul,add_zero] at ht
    exact (not_le_of_gt hF) (by rw [← ht]; exact hqA)
  have hzpos : 0<z-1 := tsub_pos_iff_lt.mpr hz
  exact one_le_mul (pos_iff_one_le.mp hq) (pos_iff_one_le.mp hzpos)
end DiophantineConsistency.ArithmeticAdaptiveConstructionTransportPositive2011
