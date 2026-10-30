import DiophantineConsistency.AdaptiveGap85Holes
import DiophantineConsistency.AdaptiveGap85Arithmetic
import DiophantineConsistency.AdaptiveDirectOrdinate86Lift

/-! Reindex the conditional literal equivalence onto ordinary witnesses. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85Lift
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveFirstRootFactor87Syntax AdaptiveDirectOrdinate86Lift
open AdaptiveGap85Literal AdaptiveGap85Holes AdaptiveGap85Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def oldIndex (i : Fin 13) : Fin 14 := if i=2 then 13 else embed i
private theorem oldLift_is_var (i : Fin 13) : oldLift i=.var (oldIndex i) := by
  by_cases h : i=2 <;> simp [oldLift,oldIndex,h]

/-- Conditional exact literal equivalence for two ordinary witness vectors. -/
theorem unshifted_zero_iff_of_relation (p : Fin 4 → ℕ) (v : Fin 14 → V)
    (h : v 1+v 13+v 2=1+v 0*(p 0:V)) :
    AdaptiveEquationSyntax2011.InternalZero
      (AdaptiveDirectOrdinate86Literal.expressionAt86 (fun j => (p j:ℤ)))
        (fun i => v (oldIndex i)) ↔
    AdaptiveEquationSyntax2011.InternalZero (expressionAt85 (fun j => (p j:ℤ)))
      (fun i => v (embed i)) := by
  have he := literal_zero_iff_of_relation p v h
  have ho : oldLift = fun i => .var (oldIndex i) := funext oldLift_is_var
  have hn : newLift = fun i => .var (embed i) := rfl
  rw [ho,hn,splitEval_subst_var,splitEval_subst_var] at he
  exact he
private theorem embed_ne_last (i : Fin 13) : embed i ≠ 13 := by
  intro h
  have hv := congrArg Fin.val h
  have hi := i.isLt
  simp only [embed,Fin.val_mk] at hv
  omega

private theorem oldIndex_ne_gap (i : Fin 13) : oldIndex i ≠ 2 := by
  by_cases h : i=2
  · simp [oldIndex,h]
  · intro he
    have hv := congrArg Fin.val he
    have hi : i.val ≠ 2 := by
      intro hval
      apply h
      exact Fin.ext hval
    simp only [oldIndex,h,if_false,embed,Fin.val_mk] at hv
    exact hi hv

/-- An actual positive old zero provides a positive gap witness for the 85
literal. The other coordinates retain the original values. -/
theorem old_zero_to_new (p : Fin 4 → ℕ) (v : Fin 14 → V)
    (hb : 0<(p 0:V)) (hv : ∀i,0<v (oldIndex i))
    (hz : AdaptiveEquationSyntax2011.InternalZero
      (AdaptiveDirectOrdinate86Literal.expressionAt86 (fun j => (p j:ℤ)))
      (fun i => v (oldIndex i))) :
    ∃ C : V, 0<C ∧ AdaptiveEquationSyntax2011.InternalZero
      (expressionAt85 (fun j => (p j:ℤ))) (fun i => if i=2 then C else v (embed i)) := by
  let q : V := 1+v 0*(p 0:V)
  let C : V := q-(v 1+v 13)
  have hpos : 0<C := by
    have ht := (AdaptiveDirectOrdinate86Transport.expressionAt_transport_positive86 p
      (fun i => v (oldIndex i)) hb hv hz).2
    simpa [C,q,oldIndex,embed] using ht
  have hr : v 1+v 13+C=q := by
    have h := (forward_gap q (v 1) (v 13) (tsub_pos_iff_lt.mp hpos)).2
    exact h
  let w := Function.update v 2 C
  have hrel : w 1+w 13+w 2=1+w 0*(p 0:V) := by simpa [w,q] using hr
  have he := unshifted_zero_iff_of_relation p w hrel
  have hold : (fun i => w (oldIndex i)) = (fun i => v (oldIndex i)) := by
    funext i
    simp [w,oldIndex_ne_gap i]
  have hnew : (fun i => w (embed i)) = (fun i => if i=2 then C else v (embed i)) := by
    funext i
    by_cases hi : i=2
    · simp [hi,w,embed]
    · have hk : embed i ≠ 2 := by
        intro hh
        apply hi
        apply Fin.ext
        have hv := congrArg Fin.val hh
        change i.val=2 at hv
        change i.val=2
        exact hv
      simp [hi,w,hk]
  rw [hold,hnew] at he
  exact ⟨C,hpos,he.mp hz⟩

/-- A new zero recovers a positive old coordinate when the still-open reverse
bound is supplied explicitly. -/
theorem new_zero_to_old_of_bound (p : Fin 4 → ℕ) (v : Fin 14 → V)
    (hbound : v 1+v 2<1+v 0*(p 0:V))
    (hz : AdaptiveEquationSyntax2011.InternalZero (expressionAt85 (fun j => (p j:ℤ)))
      (fun i => v (embed i))) :
    ∃ alpha : V, 0<alpha ∧ AdaptiveEquationSyntax2011.InternalZero
      (AdaptiveDirectOrdinate86Literal.expressionAt86 (fun j => (p j:ℤ)))
      (fun i => if i=2 then alpha else v (embed i)) := by
  let q : V := 1+v 0*(p 0:V)
  let alpha : V := q-(v 1+v 2)
  have hpos : 0<alpha := tsub_pos_iff_lt.mpr hbound
  have hr : v 1+alpha+v 2=q := (reverse_gap q (v 1) (v 2) hbound).2
  let w := Function.update v 13 alpha
  have hrel : w 1+w 13+w 2=1+w 0*(p 0:V) := by simpa [w,q] using hr
  have he := unshifted_zero_iff_of_relation p w hrel
  have hnew : (fun i => w (embed i)) = (fun i => v (embed i)) := by
    funext i
    simp [w,embed_ne_last i]
  have hold : (fun i => w (oldIndex i)) = (fun i => if i=2 then alpha else v (embed i)) := by
    funext i
    by_cases hi : i=2
    · simp [oldIndex,hi,w]
    · simp [oldIndex,hi,w,embed_ne_last i]
  rw [hold,hnew] at he
  exact ⟨alpha,hpos,he.mpr hz⟩
end DiophantineConsistency.AdaptiveGap85Lift
