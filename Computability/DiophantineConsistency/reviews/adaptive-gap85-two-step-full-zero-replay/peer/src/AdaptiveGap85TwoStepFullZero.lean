import DiophantineConsistency.AdaptiveGap85InverseOneStep
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 12000000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85TwoStepFullZero
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 AdaptiveGap85Literal
open AdaptiveGap85JointResidue AdaptiveGap85ForwardOrbitNoCross
open AdaptiveGap85InverseEntry AdaptiveGap85InverseOld AdaptiveGap85InverseOneStep
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Conditional on a gap zero with two forward-shift units of T, construct a
positive zero that needs at least two bidirectional shifts to reach the gap.
This does not assert that such a starting zero exists. -/
theorem two_step_full_zero_not_one (p : Fin 4 → ℕ) (z : Fin 13 → V)
    (hb : 0<(p 0:V)) (hb2 : 2≤z 0*(p 0:V)) (hz : ∀i,0<z i)
    (hzero : InternalZero (expressionAt85 (fun j => (p j:ℤ))) z)
    (hgapz : z 1+z 2<1+z 0*(p 0:V))
    (hT : let b := z 0*(p 0:V); let q := 1+b; let U := z 7*(q*q)
      let D := b*U*(q*q-1); D+D<z 5) :
    ∃ a m : Fin 13 → V, (∀i,0<a i) ∧ (∀i,0<m i) ∧
      InternalZero (expressionAt85 (fun j => (p j:ℤ))) a ∧
      InternalZero (expressionAt85 (fun j => (p j:ℤ))) m ∧
      ¬(a 1+a 2<1+a 0*(p 0:V)) ∧ ¬(m 1+m 2<1+m 0*(p 0:V)) ∧
      z 1+z 2<1+z 0*(p 0:V) ∧ PositiveBiStep p a m ∧ PositiveBiStep p m z ∧
      ¬∃ x : Fin 13 → V, PositiveBiStep p a x ∧ x 1+x 2<1+x 0*(p 0:V) := by
  let m : Fin 13 → V := AdaptiveGap85ShiftModel.shift p z
  let a : Fin 13 → V := AdaptiveGap85ShiftModel.shift p m
  let b : V := z 0*(p 0:V)
  let q : V := 1+b
  let U : V := z 7*(q*q)
  let D : V := b*U*(q*q-1)
  change D+D<z 5 at hT
  have hT1' : D<z 5 := lt_of_le_of_lt (by simp : D≤D+D) hT
  have hT1 : let b := z 0*(p 0:V); let q := 1+b; let U := z 7*(q*q)
      b*U*(q*q-1)<z 5 := hT1'
  obtain ⟨hm,hzm,hnotm⟩ := AdaptiveGap85ShiftModel.shifted_zero_breaks_gap p z hb hz hT1 hzero
  change (∀i,0<m i) at hm
  change InternalZero (expressionAt85 (fun j => (p j:ℤ))) m at hzm
  have hdec : (z 5-D)+D=z 5 := tsub_add_cancel_of_le (le_of_lt hT1')
  have hm0 : m 0=z 0 := rfl
  have hm7 : m 7=z 7 := rfl
  have hmD : m 0*(p 0:V)*(m 7*((1+m 0*(p 0:V))*(1+m 0*(p 0:V))))*
      ((1+m 0*(p 0:V))*(1+m 0*(p 0:V))-1)=D := by
    rw [hm0,hm7]
  have hm5 : m 5=z 5-D := rfl
  have hT2 : let b := m 0*(p 0:V); let q := 1+b; let U := m 7*(q*q)
      b*U*(q*q-1)<m 5 := by
    change m 0*(p 0:V)*(m 7*((1+m 0*(p 0:V))*(1+m 0*(p 0:V))))*
      ((1+m 0*(p 0:V))*(1+m 0*(p 0:V))-1)<m 5
    rw [hmD,hm5]
    by_contra hn
    have hle : z 5-D≤D := le_of_not_gt hn
    have hh : (z 5-D)+D≤D+D := add_le_add hle (le_refl _)
    rw [hdec] at hh
    exact (not_le_of_gt hT) hh
  obtain ⟨ha,hza,hnota⟩ := AdaptiveGap85ShiftModel.shifted_zero_breaks_gap p m hb hm hT2 hzm
  change (∀i,0<a i) at ha
  change InternalZero (expressionAt85 (fun j => (p j:ℤ))) a at hza
  have hba : 2≤a 0*(p 0:V) := by
    have ha0 : a 0=z 0 := rfl
    rw [ha0]
    exact hb2
  have hone : ¬∃ x : Fin 13 → V, PositiveBiStep p a x ∧ x 1+x 2<1+x 0*(p 0:V) := by
    intro hpath
    obtain ⟨hp,hgap⟩ := (one_step_gap_iff_candidate p a hba ha hnota).mp hpath
    have hinv : inverse p a=m := by dsimp [a]; exact inverse_shift p m (le_of_lt hT2)
    rw [hinv] at hgap
    exact hnotm hgap
  refine ⟨a,m,ha,hm,hza,hzm,hnota,hnotm,hgapz,?_,?_,hone⟩
  · exact Or.inr ⟨Or.inl rfl,hm,ha⟩
  · exact Or.inr ⟨Or.inl rfl,hz,hm⟩
end DiophantineConsistency.AdaptiveGap85TwoStepFullZero
