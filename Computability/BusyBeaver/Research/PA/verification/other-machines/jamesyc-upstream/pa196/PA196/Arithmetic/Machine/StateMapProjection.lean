module
public import PA196.Arithmetic.Machine.StateMapTrace
@[expose] public section
namespace PA196.Arithmetic.Machine.StateMap
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic
open PA PA.InternalTrace
attribute [local irreducible] StepFormula.formula Exact.PA.StepFormula.formula Step

section Models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]

def LiteralStep (q l r q' l' r' : V) : Prop :=
  V ⊧/![q,l,r,q',l',r'] Exact.PA.StepFormula.formula

private theorem literal_step_vector (b : Fin 6 → V) :
    (V ⊧/b Exact.PA.StepFormula.formula) ↔
      LiteralStep (b 0) (b 1) (b 2) (b 3) (b 4) (b 5) := by
  have hb : b=![b 0,b 1,b 2,b 3,b 4,b 5] := by simp [funext_iff,Fin.forall_fin_succ]
  unfold LiteralStep
  exact iff_of_eq (congrArg (fun v => V ⊧/v Exact.PA.StepFormula.formula) hb)

attribute [local irreducible] LiteralStep

set_option maxRecDepth 2048 in
/-- Relabel only the control vector of an internally coded auxiliary trace.
The tape vectors and every model-length time index are preserved. -/
theorem segment_to_literal {n qs ls rs lf rf : V}
    (h : Segment n qs ls rs 0 0 0 215 lf rf) :
    V ⊧/![] Exact.PA.HaltingFormula.traceSentence := by
  have hlive := segment_avoids_padding h
  rcases h with ⟨hq,_,_,hq0,hl0,hr0,hqn,_,_,hsteps⟩
  have hm {i : V} (hi : i≤n) : nth (mapVector qs) i=decodeTag (nth qs i) :=
    map_nth qs (by rw [hq]; exact lt_succ_iff_le.mpr hi)
  have hm0 : nth (mapVector qs) 0=0 := by rw [hm (by simp),hq0,decode_zero]
  have hmn : nth (mapVector qs) n=196 := by rw [hm (by simp),hqn,decode_halt]
  simp only [Exact.PA.HaltingFormula.traceSentence,Semiformula.eval_ex,
    Semiformula.eval_ballLT,LogicalConnective.HomClass.map_and]
  refine ⟨n,mapVector qs,ls,rs,?_,?_,?_,?_,?_⟩
  · simpa [nth_defined.df] using hm0.symm
  · simpa [nth_defined.df] using hl0.symm
  · simpa [nth_defined.df] using hr0.symm
  · simpa [nth_defined.df,numeral_eq_natCast] using hmn.symm
  · intro i hi
    have hi' : i<n := by simpa using hi
    have hs : LiteralStep (nth (mapVector qs) i) (nth ls i) (nth rs i)
        (nth (mapVector qs) (i+1)) (nth ls (i+1)) (nth rs (i+1)) := by
      rw [hm (le_of_lt hi'),hm (lt_succ_iff_le.mp (by simpa using hi'))]
      unfold LiteralStep
      exact step_maps _ _ _ _ _ _ (hsteps i hi') (hlive i (le_of_lt hi'))
    refine ⟨nth (mapVector qs) i,nth ls i,nth rs i,
      nth (mapVector qs) (i+1),nth ls (i+1),nth rs (i+1),?_,?_,?_,?_,?_,?_,?_⟩
    · simp [nth_defined.df]
    · simp [nth_defined.df]
    · simp [nth_defined.df]
    · simp [nth_defined.df]
    · simp [nth_defined.df]
    · simp [nth_defined.df]
    · simpa [literal_step_vector] using hs

end Models

def literalProjectionSentence : ArithmeticSentence :=
  “∀ n qs ls rs lf rf,
    !segmentFormula n qs ls rs 0 0 0 215 lf rf → !Exact.PA.HaltingFormula.traceSentence”

attribute [local irreducible] Exact.PA.HaltingFormula.traceSentence

set_option maxRecDepth 2048 in
theorem pa_proves_literal_projection : theory ⊢ literalProjectionSentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp only [literalProjectionSentence,models_iff]
  simp [segment_correct,numeral_eq_natCast]
  intro n qs ls rs lf rf h
  exact segment_to_literal h

#print axioms segment_to_literal
#print axioms pa_proves_literal_projection
end PA196.Arithmetic.Machine.StateMap
