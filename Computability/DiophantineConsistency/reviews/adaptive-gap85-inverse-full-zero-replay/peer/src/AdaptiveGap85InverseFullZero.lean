import DiophantineConsistency.AdaptiveGap85InverseBounds
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 12000000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85InverseFullZero
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs AdaptiveDirectOrdinate86Context
open AdaptiveGap85Literal AdaptiveGap85JointResidue AdaptiveGap85ForwardOrbitNoCross
open AdaptiveGap85InverseEntry AdaptiveGap85InverseBounds
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- For a positive full 85-zero outside the gap, the four explicit bounds
exactly characterize a positive full-zero gap endpoint in one bidirectional
step. The truth of the bounds remains unproved in general. -/
theorem one_step_full_zero_iff_bounds (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hb : 2≤v 0*(p 0:V)) (hv : ∀i,0<v i)
    (hz : InternalZero (expressionAt85 (fun j => (p j:ℤ))) v)
    (hnot : ¬v 1+v 2<1+v 0*(p 0:V)) :
    let b := v 0*(p 0:V)
    let q := 1+b
    let k := v 9+v 10
    let c := v 9+v 7*k
    let U := v 7*(q*q)
    let A := v 6+(p 1:V)*q
    let d := b*c*U
    (∃ w : Fin 13 → V, PositiveBiStep p v w ∧
      InternalZero (expressionAt85 (fun j => (p j:ℤ))) w ∧
      w 1+w 2<1+w 0*(p 0:V)) ↔
      d<v 2 ∧ d*A*k+c*U*A<v 8 ∧ b*c*(q*q-1)<v 12 ∧
      v 1+(v 2-d)<q := by
  constructor
  · rintro ⟨w,hstep,_,hgap⟩
    exact (one_step_gap_iff_bounds p v hb hv hnot).mp ⟨w,hstep,hgap⟩
  · intro hbounds
    obtain ⟨w,hstep,hgap⟩ := (one_step_gap_iff_bounds p v hb hv hnot).mpr hbounds
    have he := entry_requires_inverse_old p v w hb hstep hnot hgap
    have ht : let b := w 0*(p 0:V); let q := 1+b; let U := w 7*(q*q)
        b*U*(q*q-1)≤w 5 := by
      have h5 := hv 5
      rw [he] at h5
      change 0<w 5-(w 0*(p 0:V))*(w 7*((1+w 0*(p 0:V))*(1+w 0*(p 0:V))))*
        ((1+w 0*(p 0:V))*(1+w 0*(p 0:V))-1) at h5
      exact le_of_lt (tsub_pos_iff_lt.mp h5)
    have hpres := AdaptiveGap85ShiftModel.literal_preserved p w ht
    rw [←he] at hpres
    exact ⟨w,hstep,(equivalent_zero_iff hpres).1 hz,hgap⟩
end DiophantineConsistency.AdaptiveGap85InverseFullZero
