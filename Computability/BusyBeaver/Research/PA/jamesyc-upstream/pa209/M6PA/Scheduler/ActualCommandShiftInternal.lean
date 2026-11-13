module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.ActualCommandLiteralInternal
public import M6PA.Scheduler.ActualCommandTagInternal
@[expose] public section
open M6.Arithmetic.PA
namespace M6.PA.ActualCommandStepGraph
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open SourceCantorInternal ActualHeadGraphs ActualCommandWordGraph ActualCommandLiteralInternal
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

@[simp] theorem source_left_pair (a b : V) : decodeLeft (pairValue a b)=a := (decode_pairValue a b).1
@[simp] theorem source_right_pair (a b : V) : decodeRight (pairValue a b)=b := (decode_pairValue a b).2
@[simp] theorem sparse_zero : Sparse (0 : V) := Or.inl rfl

theorem shift_sparse (t x w d h : V) (ht : Sparse t) (hh : Sparse h) :
    stepValue 0 (stateCode t (pairValue x w) d h)=stateCode h w d x := by
  rw [shift_value,if_neg (sparse_add_ne_one ht hh)]
  simp only [source_left_pair,source_right_pair]

noncomputable def axThenShifts (c x y : V) (n : Nat) : V :=
  axCode c x y ∷ literalValue (List.replicate n 0)

/-- Ten literal shifts safely discharge all nine actual heads, retaining the
saved top in H. The theorem applies to arbitrary model-valued parameters. -/
theorem ax_shift10_value (c x y t w d h : V) :
    wordValue (axThenShifts c x y 10) (stateCode t w d h)=
      stateCode (ActualArithmeticGraph.eval universalExpr d h 0 0) w 0 t := by
  have hs := schemaHeads_sparse (d+x) (h+y) c d h
  simp only [schemaHeads,List.forall_mem_cons,List.forall_mem_nil,and_true] at hs
  rcases hs with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩
  have hg := gate_sparse (d+x) (h+y) c d
  rw [axThenShifts,word_cons,ax_value]
  simp only [literalValue,List.replicate_succ,List.replicate_zero,List.foldr_cons,List.foldr_nil,
    List.cons_append,List.nil_append,schemaHeads,word_cons,word_zero,Nat.cast_zero,
    shift_sparse,hg,sparse_zero,h1,h2,h3,h4,h5,h6,h7,h8,h9]

theorem ax_shift_succ (c x y s : V) (n : Nat) :
    wordValue (axThenShifts c x y (n+1)) s=
      stepValue 0 (wordValue (axThenShifts c x y n) s) := by
  have hw : axThenShifts c x y (n+1)=
      InternalTrace.HFSAppend.append (axThenShifts c x y n) (0 ∷ (0 : V)) := by
    simp only [axThenShifts,List.replicate_succ',literal_append,literal_cons,literal_nil,
      Nat.cast_zero,InternalTrace.HFSAppend.append_adjoin]
  rw [hw,word_append,word_cons,word_zero]

/-- The final head is at least two, so popping the saved top is safe even
when that top itself is one. -/
theorem ax_shift11_value (c x y t w d h : V) :
    wordValue (axThenShifts c x y 11) (stateCode t w d h)=
      stateCode t (decodeRight w) 0 (decodeLeft w) := by
  rw [show (11 : Nat)=10+1 by decide,ax_shift_succ,ax_shift10_value,shift_value,
    if_neg (universal_add_ne_one d h t)]

#print axioms ax_shift11_value

#print axioms shift_sparse
#print axioms ax_shift10_value
end M6.PA.ActualCommandStepGraph
