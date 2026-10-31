import DiophantineConsistency.AdaptiveGap85OrientedRank
import DiophantineConsistency.AdaptiveGap85PortBoundary
import DiophantineConsistency.ArithmeticAdaptiveScaledNorms2011

/-! Conditional digit bounds at an actual 85 zero. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85ActualPortBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticPellRecurrence ArithmeticPellHalfIndex
open ArithmeticAdaptiveScaledNorms2011 AdaptiveGap85Literal AdaptiveGap85OrientedRank
open AdaptiveGap85PortBound AdaptiveGap85PortBoundary
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- With bounded ports and an explicit small-rank hypothesis, an actual 85 zero
forces qF+C<q²+2 and F≤q; at equality F=q it forces C=1. -/
theorem expressionAt_port_bounds85 (p : Fin 4 → ℕ) (v : Fin 13 → V) (n : V)
    (hb : 0<(p 0:V)) (hv : ∀ j,0<v j)
    (hMC : (p 2:V)≤(p 0:V)) (hMF : (p 3:V)≤2*(p 0:V))
    (hz : InternalZero (expressionAt85 (fun j => (p j:ℤ))) v)
    (hn : 0<n) (hny : 2*ycoord n (2*((v 6*v 7)*v 7-1)+1)=v 9+v 10)
    (hsmall : let q : V := 1+v 0*(p 0:V)
      let q2 : V := q*q
      let neg : V := q*v 1+v 2
      let rp : V := q2*q2+neg+v 0*((p 2:V)+(p 3:V)*q)
      let rn : V := q2+neg*q2
      absdiff rp rn+2*n<q^4) :
    let q : V := 1+v 0*(p 0:V)
    q*v 1+v 2<q*q+2 ∧ v 1≤q ∧ (v 1=q → v 2=1) := by
  have ho := expressionAt_oriented_rank85 p v n hb hv hz hn hny hsmall
  have hrank := ho.1
  have hw := weighted_bound_of_bounded_ports (p 0:V) (v 0) (p 2:V) (p 3:V) (v 1) (v 2) hMC hMF hrank
  have hq0 : (1:V)<1+v 0*(p 0:V) := (scaled_parameters_positive p v hb hv).1
  have hq : (2:V)≤1+v 0*(p 0:V) := by
    simpa only [one_add_one_eq_two] using (lt_iff_succ_le.mp hq0)
  have hf := F_le_q_of_bounded_ports (p 0:V) (v 0) (p 2:V) (p 3:V) (v 1) (v 2) hq (hv 2) hMC hMF hrank
  have hc := C_eq_one_if_F_eq_q (p 0:V) (v 0) (p 2:V) (p 3:V) (v 1) (v 2) (hv 2) hMC hMF hrank
  exact ⟨hw,hf,hc⟩
end DiophantineConsistency.AdaptiveGap85ActualPortBound
