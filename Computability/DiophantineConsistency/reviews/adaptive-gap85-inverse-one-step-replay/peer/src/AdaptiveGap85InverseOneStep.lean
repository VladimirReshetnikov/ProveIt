import DiophantineConsistency.AdaptiveGap85InverseEntry
import DiophantineConsistency.AdaptiveGap85InverseOld
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 12000000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85InverseOneStep
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 AdaptiveGap85Literal
open AdaptiveGap85JointResidue AdaptiveGap85ForwardOrbitNoCross
open AdaptiveGap85InverseEntry AdaptiveGap85InverseOld
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Outside the gap, one positive step in either direction reaches it iff
the explicit inverse-old candidate is positive and has the gap. The
coordinate relation is broader than zero-preserving moves. -/
theorem one_step_gap_iff_candidate (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hb : 2≤v 0*(p 0:V)) (hv : ∀i,0<v i)
    (hnot : ¬v 1+v 2<1+v 0*(p 0:V)) :
    (∃ w : Fin 13 → V, PositiveBiStep p v w ∧
      w 1+w 2<1+w 0*(p 0:V)) ↔
    (∀i,0 < inverse p v i) ∧
      inverse p v 1+inverse p v 2<1+inverse p v 0*(p 0:V) := by
  constructor
  · rintro ⟨w,hstep,hgap⟩
    have he := entry_requires_inverse_old p v w hb hstep hnot hgap
    have hw : ∀i,0<w i := by
      rcases hstep with h | h
      · exact h.2.2
      · exact h.2.1
    have ht : let b := w 0*(p 0:V); let q := 1+b; let U := w 7*(q*q)
        b*U*(q*q-1)≤w 5 := by
      have h5 := hv 5
      rw [he] at h5
      change 0<w 5-(w 0*(p 0:V))*(w 7*((1+w 0*(p 0:V))*(1+w 0*(p 0:V))))*
        ((1+w 0*(p 0:V))*(1+w 0*(p 0:V))-1) at h5
      exact le_of_lt (tsub_pos_iff_lt.mp h5)
    have hinv : inverse p v=w := by rw [he]; exact inverse_shift p w ht
    rw [hinv]
    exact ⟨hw,hgap⟩
  · rintro ⟨hw,hgap⟩
    have hC : let b := v 0*(p 0:V); let q := 1+b; let U := v 7*(q*q)
        let c := v 9+v 7*(v 9+v 10); b*c*U≤v 2 := by
      have h2 := hw 2
      change 0<v 2-(v 0*(p 0:V))*(v 9+v 7*(v 9+v 10))*
        (v 7*((1+v 0*(p 0:V))*(1+v 0*(p 0:V)))) at h2
      exact le_of_lt (tsub_pos_iff_lt.mp h2)
    have hr : let b := v 0*(p 0:V); let q := 1+b; let U := v 7*(q*q)
        let c := v 9+v 7*(v 9+v 10); let A := v 6+(p 1:V)*q
        (b*c*U)*A*(v 9+v 10)+c*U*A≤v 8 := by
      have h8 := hw 8
      change 0<v 8-((v 0*(p 0:V))*(v 9+v 7*(v 9+v 10))*
        (v 7*((1+v 0*(p 0:V))*(1+v 0*(p 0:V))))*
        (v 6+(p 1:V)*(1+v 0*(p 0:V)))*(v 9+v 10)+
        (v 9+v 7*(v 9+v 10))*(v 7*((1+v 0*(p 0:V))*(1+v 0*(p 0:V))))*
        (v 6+(p 1:V)*(1+v 0*(p 0:V)))) at h8
      exact le_of_lt (tsub_pos_iff_lt.mp h8)
    have hg : let b := v 0*(p 0:V); let q := 1+b; let c := v 9+v 7*(v 9+v 10)
        b*c*(q*q-1)≤v 12 := by
      have h12 := hw 12
      change 0<v 12-(v 0*(p 0:V))*(v 9+v 7*(v 9+v 10))*
        ((1+v 0*(p 0:V))*(1+v 0*(p 0:V))-1) at h12
      exact le_of_lt (tsub_pos_iff_lt.mp h12)
    have he := shift_inverse p v hC hr hg
    refine ⟨inverse p v,Or.inr ⟨Or.inl he.symm,hw,hv⟩,hgap⟩
/-- A positive 85-zero outside the gap transfers to 86 if any of these
single positive coordinate steps reaches the gap. -/
theorem one_step_gap_zero_to_86 (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hb : 2≤v 0*(p 0:V)) (hv : ∀i,0<v i)
    (hz : InternalZero (expressionAt85 (fun j => (p j:ℤ))) v)
    (hnot : ¬v 1+v 2<1+v 0*(p 0:V))
    (hstep : ∃ w : Fin 13 → V, PositiveBiStep p v w ∧
      w 1+w 2<1+w 0*(p 0:V)) :
    ∃ u : Fin 13 → V, InternalZero
      (positiveShift (AdaptiveDirectOrdinate86Literal.expressionAt86 (fun j => (p j:ℤ)))) u := by
  obtain ⟨hw,hgap⟩ := (one_step_gap_iff_candidate p v hb hv hnot).mp hstep
  have hC : let b := v 0*(p 0:V); let q := 1+b; let U := v 7*(q*q)
      let c := v 9+v 7*(v 9+v 10); b*c*U<v 2 := by
    have h2 := hw 2
    change 0<v 2-(v 0*(p 0:V))*(v 9+v 7*(v 9+v 10))*
      (v 7*((1+v 0*(p 0:V))*(1+v 0*(p 0:V)))) at h2
    exact tsub_pos_iff_lt.mp h2
  have hr : let b := v 0*(p 0:V); let q := 1+b; let U := v 7*(q*q)
      let c := v 9+v 7*(v 9+v 10); let A := v 6+(p 1:V)*q
      (b*c*U)*A*(v 9+v 10)+c*U*A<v 8 := by
    have h8 := hw 8
    change 0<v 8-((v 0*(p 0:V))*(v 9+v 7*(v 9+v 10))*
      (v 7*((1+v 0*(p 0:V))*(1+v 0*(p 0:V))))*
      (v 6+(p 1:V)*(1+v 0*(p 0:V)))*(v 9+v 10)+
      (v 9+v 7*(v 9+v 10))*(v 7*((1+v 0*(p 0:V))*(1+v 0*(p 0:V))))*
      (v 6+(p 1:V)*(1+v 0*(p 0:V)))) at h8
    exact tsub_pos_iff_lt.mp h8
  have hg : let b := v 0*(p 0:V); let q := 1+b; let c := v 9+v 7*(v 9+v 10)
      b*c*(q*q-1)<v 12 := by
    have h12 := hw 12
    change 0<v 12-(v 0*(p 0:V))*(v 9+v 7*(v 9+v 10))*
      ((1+v 0*(p 0:V))*(1+v 0*(p 0:V))-1) at h12
    exact tsub_pos_iff_lt.mp h12
  exact inverse_old_zero_to_86 p v hv hz hC hr hg hgap
end DiophantineConsistency.AdaptiveGap85InverseOneStep
