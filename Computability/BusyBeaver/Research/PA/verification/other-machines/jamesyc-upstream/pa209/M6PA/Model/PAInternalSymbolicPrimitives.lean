module
/- M6 PA-model runtime port. This is a fresh append-one/table adaptation;
its theorem scope is not the completed PA-unprovability endpoint. -/
public import M6PA.Model.PAInternalSymbolicPeel
@[expose] public section
namespace M6.Arithmetic.PA.InternalTrace.Symbolic
open M6
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic
open ScanBits M6.Runtime
attribute [local irreducible] Step StepFormula.formula
section Models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]

def Progress (m : Bool) (s t : ModelConf V) : Prop :=
  ∃ k qs ls rs, Segment k qs ls rs s.q s.left s.right t.q t.left t.right ∧ (m=true → 0<k)

theorem progress_eq {s t : ModelConf V} (h : s=t) : Progress false s t := by
  subst t
  exact ⟨0,_,_,_,segment_zero s.q s.left s.right,by simp⟩
theorem progress_one {s t : ModelConf V} (h : Step s.q s.left s.right t.q t.left t.right) :
    Progress true s t := by
  exact ⟨1,_,_,_,segment_one h,by simp⟩
theorem progress_trans {s t u : ModelConf V} {m n : Bool}
    (h : Progress m s t) (g : Progress n t u) : Progress (m || n) s u := by
  obtain ⟨a,qa,la,ra,ha,hpa⟩ := h
  obtain ⟨b,qb,lb,rb,hb,hpb⟩ := g
  obtain ⟨q,l,r,hab⟩ := segment_compose ha hb
  refine ⟨a+b,q,l,r,hab,?_⟩
  intro hm
  have hor : m=true ∨ n=true := by cases m <;> cases n <;> simp_all
  rcases hor with hm | hn
  · exact lt_of_lt_of_le (hpa hm) (by simp)
  · exact lt_of_lt_of_le (hpb hn) (by simp)

noncomputable def denseControl (q : Nat) : V := NativeRows.code q

variable (n : V) (box : BoxSt → V → V)
theorem bit_right {q q' : Nat} {b w : Bool} (l r : List Seg)
    (h : NativeTable.machine q b=some (w,true,q')) :
    Progress true (config n box denseControl (q,false,l,.bit b::r))
      (config n box denseControl (q',false,.bit w::l,r)) := by
  apply progress_one
  simpa [config,word,denseControl] using
    (NativeRows.right h (word n box l 0) (word n box r 0))

theorem bit_left {q q' : Nat} {b w : Bool} (l r : List Seg)
    (h : NativeTable.machine q b=some (w,false,q')) :
    Progress true (config n box denseControl (q,false,l,.bit b::r))
      (config n box denseControl (q',true,l,.bit w::r)) := by
  apply progress_one
  simpa [config,word,denseControl] using
    (NativeRows.left h (word n box l 0) (word n box r 0))

theorem run_right {q : Nat} {b w : Bool} (a c : Nat) (l r : List Seg)
    (h : NativeTable.machine q b=some (w,true,q)) :
    Progress false (config n box denseControl (q,false,l,.run b a c::r))
      (config n box denseControl (q,false,.run w a c::l,r)) := by
  obtain ⟨qs,ls,rs,hs⟩ := NativeRows.scan_right h ((a : V)*n+c) (word n box l 0) (word n box r 0)
  refine ⟨(a : V)*n+c,qs,ls,rs,?_,by simp⟩
  simpa [config,word,denseControl] using hs

theorem run_left {q : Nat} {b w : Bool} (a c : Nat) (l r : List Seg)
    (h : NativeTable.machine q b=some (w,false,q)) :
    Progress false (config n box denseControl (q,true,.run b a c::l,r))
      (config n box denseControl (q,true,l,.run w a c::r)) := by
  obtain ⟨qs,ls,rs,hs⟩ := NativeRows.scan_left h ((a : V)*n+c) (word n box l 0) (word n box r 0)
  refine ⟨(a : V)*n+c,qs,ls,rs,?_,by simp⟩
  simpa [config,word,denseControl,Phase] using hs
end Models
#print axioms progress_trans
#print axioms bit_right
#print axioms bit_left
#print axioms run_right
#print axioms run_left
end M6.Arithmetic.PA.InternalTrace.Symbolic

