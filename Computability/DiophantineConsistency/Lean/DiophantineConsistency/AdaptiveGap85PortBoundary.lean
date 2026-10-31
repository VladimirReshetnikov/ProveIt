import DiophantineConsistency.AdaptiveGap85PortBound

/-! The boundary case of a positive signed rank and bounded ports. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85PortBoundary
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveGap85PortBound
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- If F reaches q, the weighted bound forces C to be exactly one. -/
theorem C_eq_one_if_F_eq_q (beta J MC MF F C : V)
    (hC : 0<C) (hMC : MC≤beta) (hMF : MF≤2*beta)
    (hrank : let q := 1+J*beta
      q*q+(q*F+C)*(q*q)<(q*q)*(q*q)+(q*F+C)+J*(MC+MF*q))
    (hF : F=1+J*beta) : C=1 := by
  let q : V := 1+J*beta
  have hw := weighted_bound_of_bounded_ports beta J MC MF F C hMC hMF hrank
  change q*F+C<q*q+2 at hw
  change F=q at hF
  rw [hF] at hw
  have hC2 : C<2 := (add_lt_add_iff_left (q*q)).mp hw
  have hC1 : 1≤C := pos_iff_one_le.mp hC
  have hsucc : C+1≤(1:V)+1 := by
    simpa only [one_add_one_eq_two] using (lt_iff_succ_le.mp hC2)
  have hle : C≤1 := (add_le_add_iff_right (1:V)).mp hsucc
  exact le_antisymm hle hC1
end DiophantineConsistency.AdaptiveGap85PortBoundary
