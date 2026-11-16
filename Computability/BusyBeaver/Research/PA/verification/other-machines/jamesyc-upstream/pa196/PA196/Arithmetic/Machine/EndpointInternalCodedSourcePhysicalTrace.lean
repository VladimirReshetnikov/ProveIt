module
public import PA196.Arithmetic.Machine.PATheory
public import PA196.Arithmetic.Machine.EndpointInternalCodedSourcePhysicalStep
@[expose] public section
namespace PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource
open M6 PA196.Arithmetic.Machine.PA
open PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open Symbolic
attribute [local irreducible] stepValue stepGraph traceGraph frameGraph Step StepFormula.formula

/-- Either a positive halt trace is already available, or a whole-file frame
and a physical trace have been retained at this source state. -/
def liftFormula : ArithmeticSemisentence 4 :=
  “c q0 l0 r0.
    (∃ k qs ls rs lf rf, 0<k ∧ !segmentFormula k qs ls rs q0 l0 r0 215 lf rf) ∨
    (∃ n xs q l r k qs ls rs,
      !frameGraph c n xs q l r ∧ !segmentFormula k qs ls rs q0 l0 r0 q l r)”
def liftInvariantFormula : ArithmeticSemisentence 1 :=
  “i. ∀ n cs a b padding file q l r,
    !traceGraph n cs a b ∧ !frameGraph a padding file q l r → i≤n →
    ∃ c, !nthDef c cs i ∧ !liftFormula c q l r”

section Models
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
def Lifted (c q0 l0 r0 : V) : Prop :=
  (∃ k qs ls rs lf rf, 0<k ∧ Segment k qs ls rs q0 l0 r0 215 lf rf) ∨
  (∃ n xs q l r k qs ls rs,
    Refines c n xs ⟨q,l,r⟩ ∧ Segment k qs ls rs q0 l0 r0 q l r)

lemma lift_correct (v : Fin 4 → V) : (V ⊧/v liftFormula) ↔
    Lifted (v 0) (v 1) (v 2) (v 3) := by
  simp [liftFormula,Lifted,segment_correct,frame_correct,numeral_eq_natCast,Nat.cast_ofNat]

lemma lift_initial {a n xs q l r : V} (h : Refines a n xs ⟨q,l,r⟩) : Lifted a q l r := by
  exact Or.inr ⟨n,xs,q,l,r,0,_,_,_,h,segment_zero q l r⟩

lemma lift_step {c q0 l0 r0 : V} (h : Lifted c q0 l0 r0) :
    Lifted (stepValue c) q0 l0 r0 := by
  rcases h with hh | ⟨n,xs,q,l,r,k,qs,ls,rs,hframe,hseg⟩
  · exact Or.inl hh
  · rcases physical_step hframe with hh | ⟨n',xs',m',hframe',hprogress⟩
    · obtain ⟨j,qj,lj,rj,lf,rf,hpos,hj⟩ := hh
      obtain ⟨qall,lall,rall,hall⟩ := segment_compose hseg hj
      exact Or.inl ⟨k+j,qall,lall,rall,lf,rf,lt_of_lt_of_le hpos (by simp),hall⟩
    · obtain ⟨j,qj,lj,rj,hj,hpos⟩ := hprogress
      obtain ⟨qall,lall,rall,hall⟩ := segment_compose hseg hj
      exact Or.inr ⟨n',xs',m'.q,m'.left,m'.right,k+j,qall,lall,rall,hframe',hall⟩

lemma liftInvariant_correct (i : V) : (V ⊧/![i] liftInvariantFormula) ↔
    ∀ n cs a b padding file q l r : V,
      Trace n cs a b → Refines a padding file ⟨q,l,r⟩ → i≤n → Lifted cs.[i] q l r := by
  simp [liftInvariantFormula,trace_correct,frame_correct,nth_defined.df,lift_correct]

/-- Genuine all-model PA induction. It retains the full physical HFS file and
padding existentially; it does not iterate an external Nat source trace. -/
theorem trace_physical_lift {n cs a b padding file q l r : V}
    (h : Trace n cs a b) (hf : Refines a padding file ⟨q,l,r⟩) : Lifted b q l r := by
  letI : InductionScheme ℒₒᵣ Set.univ ⪯ theory :=
    Entailment.WeakerThan.ofSubset Set.subset_union_right
  haveI : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ :=
    models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have all : ∀ i : V, ∀ n cs a b padding file q l r : V,
      Trace n cs a b → Refines a padding file ⟨q,l,r⟩ → i≤n → Lifted cs.[i] q l r := by
    refine InductionScheme.succ_induction (C := Set.univ)
      (P := fun i : V => ∀ n cs a b padding file q l r : V,
        Trace n cs a b → Refines a padding file ⟨q,l,r⟩ → i≤n → Lifted cs.[i] q l r) ?_ ?_ ?_
    · refine ⟨fun _ => 0,Rewriting.emb liftInvariantFormula,by trivial,?_⟩
      intro i; simpa using (liftInvariant_correct i).symm
    · intro n cs a b padding file q l r ht hf hi
      rw [ht.2.1]
      exact lift_initial hf
    · intro i ih n cs a b padding file q l r ht hf hi
      have hin : i<n := lt_of_lt_of_le (by simp) hi
      have old := ih n cs a b padding file q l r ht hf (le_of_lt hin)
      rw [ht.2.2.2 i hin]
      exact lift_step old
  have hlast := all n n cs a b padding file q l r h hf (le_refl n)
  simpa only [h.2.2.1] using hlast

/-- A model-length literal source halt trace produces an actual positive
machine halt trace from the exactly related full physical frame. -/
theorem trace_halt_physical {n cs a b padding file q l r : V}
    (h : Trace n cs a b) (hf : Refines a padding file ⟨q,l,r⟩) (hb : PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource.control b=0) :
    ∃ k qs ls rs lf rf, 0<k ∧ Segment k qs ls rs q l r 215 lf rf := by
  rcases trace_physical_lift h hf with hh | ⟨np,xp,qp,lp,rp,k,qs,ls,rs,hbframe,hseg⟩
  · exact hh
  · obtain ⟨i,s,hs,hpc,hm⟩ := frames_cases hbframe.2.2.2
    rw [hb] at hpc
    have hn : ((i+1 : Nat) : V)≠0 := by exact_mod_cast (show i+1≠0 by omega)
    exact False.elim (hn hpc.symm)
end Models

def sourceHaltingRefinementSentence : ArithmeticSentence :=
  “∀ n cs a b padding file q l r,
    !traceGraph n cs a b ∧ !frameGraph a padding file q l r ∧ !fstIdxDef 0 b →
    ∃ k qs ls rs lf rf, 0<k ∧ !segmentFormula k qs ls rs q l r 215 lf rf”

theorem pa_proves_source_halting_refinement : theory ⊢ sourceHaltingRefinementSentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp only [sourceHaltingRefinementSentence,models_iff]
  simp [trace_correct,frame_correct,fstIdx_defined.df,segment_correct]
  intro n cs a b padding file q l r h hf hb
  simpa [numeral_eq_natCast,Nat.cast_ofNat] using
    trace_halt_physical h hf (by simpa only [PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource.control,eq_comm] using hb)
#print axioms lift_step
#print axioms trace_physical_lift
#print axioms trace_halt_physical
#print axioms pa_proves_source_halting_refinement
end PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource

