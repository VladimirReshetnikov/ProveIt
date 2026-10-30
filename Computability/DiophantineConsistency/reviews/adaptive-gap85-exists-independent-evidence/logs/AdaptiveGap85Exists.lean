import DiophantineConsistency.AdaptiveGap85Lift
import DiophantineConsistency.AdaptiveDirectOrdinate86Witness

/-! Shifted existential witness transfers, with the reverse bound explicit. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85Exists
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 AdaptiveGap85Literal AdaptiveGap85Lift
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def extend (u : Fin 13 → V) (last : V) : Fin 14 → V :=
  fun i => if h : i.val<13 then u ⟨i.val,h⟩ else last

omit [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
theorem extend_embed (u : Fin 13 → V) (last : V) (i : Fin 13) :
    extend u last (embed i)=u i := by
  simp [extend,embed,i.isLt]

omit [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
theorem extend_last (u : Fin 13 → V) (last : V) : extend u last 13=last := by
  simp [extend]

/-- Every positive unshifted 86 zero gives a positive unshifted 85 zero. -/
theorem positive_old_zero_to_new (p : Fin 4 → ℕ) (u : Fin 13 → V)
    (hb : 0<(p 0:V)) (hu : ∀i,0<u i)
    (hz : InternalZero (AdaptiveDirectOrdinate86Literal.expressionAt86 (fun j => (p j:ℤ))) u) :
    ∃ w : Fin 13 → V, (∀i,0<w i) ∧ InternalZero (expressionAt85 (fun j => (p j:ℤ))) w := by
  let v : Fin 14 → V := extend u (u 2)
  have hval : (fun i => v (oldIndex i))=u := by
    funext i
    by_cases hi : i=2
    · simp [oldIndex,hi,v,extend_last]
    · simp [oldIndex,hi,v,extend_embed]
  have hv : ∀i,0<v (oldIndex i) := by
    intro i
    have hi := congrFun hval i
    rw [hi]
    exact hu i
  have hzv : InternalZero (AdaptiveDirectOrdinate86Literal.expressionAt86 (fun j => (p j:ℤ)))
      (fun i => v (oldIndex i)) := by simpa only [hval] using hz
  obtain ⟨C,hC,hnew⟩ := old_zero_to_new p v hb hv hzv
  let w : Fin 13 → V := fun i => if i=2 then C else u i
  have hw : ∀i,0<w i := by
    intro i
    by_cases hi : i=2
    · simpa [w,hi] using hC
    · simpa [w,hi] using hu i
  refine ⟨w,hw,?_⟩
  simpa only [w,v,extend_embed] using hnew

/-- Every natural zero of the shifted 86 literal yields one of the 85 literal. -/
theorem old_natural_zero_to_new (p : Fin 4 → ℕ) (u : Fin 13 → V)
    (hb : 0<(p 0:V))
    (hz : InternalZero (positiveShift (AdaptiveDirectOrdinate86Literal.expressionAt86 (fun j => (p j:ℤ)))) u) :
    ∃ w : Fin 13 → V, InternalZero (positiveShift (expressionAt85 (fun j => (p j:ℤ)))) w := by
  have hu : ∀i,0<u i+1 := by intro i; simp
  have hzu : InternalZero (AdaptiveDirectOrdinate86Literal.expressionAt86 (fun j => (p j:ℤ)))
      (fun i => u i+1) := (internalZero_positiveShift _ _).mp hz
  obtain ⟨w,hw,hwz⟩ := positive_old_zero_to_new p (fun i => u i+1) hb hu hzu
  exact ⟨fun i => w i-1, AdaptiveDirectOrdinate86Witness.shifted_zero_of_positive hw hwz⟩
/-- No natural 85 zero implies no natural 86 zero, in every model. -/
theorem new_no_zero_implies_old (p : Fin 4 → ℕ) (hb : 0<(p 0:V))
    (hnew : ∀ w : Fin 13 → V, ¬InternalZero (positiveShift (expressionAt85 (fun j => (p j:ℤ)))) w) :
    ∀ u : Fin 13 → V, ¬InternalZero
      (positiveShift (AdaptiveDirectOrdinate86Literal.expressionAt86 (fun j => (p j:ℤ)))) u := by
  intro u hz
  obtain ⟨w,hw⟩ := old_natural_zero_to_new p u hb hz
  exact hnew w hw
/-- The converse natural-zero transfer under the explicit reverse bound. -/
theorem new_natural_zero_to_old_of_bound (p : Fin 4 → ℕ) (u : Fin 13 → V)
    (hbound : (u 1+1)+(u 2+1)<1+(u 0+1)*(p 0:V))
    (hz : InternalZero (positiveShift (expressionAt85 (fun j => (p j:ℤ)))) u) :
    ∃ w : Fin 13 → V, InternalZero
      (positiveShift (AdaptiveDirectOrdinate86Literal.expressionAt86 (fun j => (p j:ℤ)))) w := by
  let t : Fin 13 → V := fun i => u i+1
  let v : Fin 14 → V := extend t 0
  have hboundv : v 1+v 2<1+v 0*(p 0:V) := by simpa [v,t,extend] using hbound
  have hzv : InternalZero (expressionAt85 (fun j => (p j:ℤ))) (fun i => v (embed i)) := by
    have h := (internalZero_positiveShift (expressionAt85 (fun j => (p j:ℤ))) u).mp hz
    simpa only [v,extend_embed,t] using h
  obtain ⟨alpha,ha,hold⟩ := new_zero_to_old_of_bound p v hboundv hzv
  let w : Fin 13 → V := fun i => if i=2 then alpha else v (embed i)
  have hw : ∀i,0<w i := by
    intro i
    by_cases hi : i=2
    · simpa [w,hi] using ha
    · simp [w,hi,v,t,extend_embed]
  exact ⟨fun i => w i-1, AdaptiveDirectOrdinate86Witness.shifted_zero_of_positive hw hold⟩

/-- Full no-zero equivalence if all candidate zeros satisfy the reverse bound. -/
theorem no_zero_iff_of_bound (p : Fin 4 → ℕ) (hb : 0<(p 0:V))
    (hbound : ∀ u : Fin 13 → V, InternalZero (positiveShift (expressionAt85 (fun j => (p j:ℤ)))) u →
      (u 1+1)+(u 2+1)<1+(u 0+1)*(p 0:V)) :
    (∀ u : Fin 13 → V, ¬InternalZero (positiveShift (expressionAt85 (fun j => (p j:ℤ)))) u) ↔
    (∀ u : Fin 13 → V, ¬InternalZero
      (positiveShift (AdaptiveDirectOrdinate86Literal.expressionAt86 (fun j => (p j:ℤ)))) u) := by
  constructor
  · exact new_no_zero_implies_old p hb
  · intro hold u hz
    obtain ⟨w,hw⟩ := new_natural_zero_to_old_of_bound p u (hbound u hz) hz
    exact hold w hw
end DiophantineConsistency.AdaptiveGap85Exists
