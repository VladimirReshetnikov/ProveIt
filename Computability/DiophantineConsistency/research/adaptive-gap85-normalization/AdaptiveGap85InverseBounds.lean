import DiophantineConsistency.AdaptiveGap85InverseOneStep
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 12000000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85InverseBounds
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 AdaptiveGap85Literal
open AdaptiveGap85JointResidue AdaptiveGap85ForwardOrbitNoCross
open AdaptiveGap85InverseEntry AdaptiveGap85InverseOld AdaptiveGap85InverseOneStep
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Four concrete arithmetic inequalities are equivalent to the existence of
one positive bidirectional gap-entering coordinate step. -/
theorem one_step_gap_iff_bounds (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hb : 2≤v 0*(p 0:V)) (hv : ∀i,0<v i)
    (hnot : ¬v 1+v 2<1+v 0*(p 0:V)) :
    let b := v 0*(p 0:V)
    let q := 1+b
    let k := v 9+v 10
    let c := v 9+v 7*k
    let U := v 7*(q*q)
    let A := v 6+(p 1:V)*q
    let d := b*c*U
    (∃ w : Fin 13 → V, PositiveBiStep p v w ∧
      w 1+w 2<1+w 0*(p 0:V)) ↔
      d<v 2 ∧ d*A*k+c*U*A<v 8 ∧ b*c*(q*q-1)<v 12 ∧
      v 1+(v 2-d)<q := by
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  let k : V := v 9+v 10
  let c : V := v 9+v 7*k
  let U : V := v 7*(q*q)
  let A : V := v 6+(p 1:V)*q
  let d : V := b*c*U
  change (∃ w : Fin 13 → V, PositiveBiStep p v w ∧
      w 1+w 2<1+w 0*(p 0:V)) ↔
      d<v 2 ∧ d*A*k+c*U*A<v 8 ∧ b*c*(q*q-1)<v 12 ∧ v 1+(v 2-d)<q
  rw [one_step_gap_iff_candidate p v hb hv hnot]
  constructor
  · rintro ⟨hw,hgap⟩
    have hc : d<v 2 := by
      have h2 := hw 2
      change 0<v 2-d at h2
      exact tsub_pos_iff_lt.mp h2
    have hr : d*A*k+c*U*A<v 8 := by
      have h8 := hw 8
      change 0<v 8-(d*A*k+c*U*A) at h8
      exact tsub_pos_iff_lt.mp h8
    have hg : b*c*(q*q-1)<v 12 := by
      have h12 := hw 12
      change 0<v 12-b*c*(q*q-1) at h12
      exact tsub_pos_iff_lt.mp h12
    exact ⟨hc,hr,hg,hgap⟩
  · rintro ⟨hc,hr,hg,hgap⟩
    exact ⟨inverse_positive p v hv hc hr hg,hgap⟩
end DiophantineConsistency.AdaptiveGap85InverseBounds
