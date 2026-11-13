module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.ActualCommandMPWordInternal
@[expose] public section
open M6.Arithmetic.PA
namespace M6.PA.ActualCommandStepGraph
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open SourceCantorInternal ActualCommandWordGraph ActualCommandLiteralInternal
open M6.Source M6.Source.CommandAtomEncoding M6.Source.ActualCommandMacros
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem popHeads_value_zero (s : V) : wordValue (literalValue (atoms (popHeads 0))) s=s := by
  simp [popHeads,atoms]

theorem popHeads_value_succ (n : Nat) (t x w d h : V) :
    wordValue (literalValue (atoms (popHeads (n+1)))) (stateCode t (pairValue x w) d h)=
      wordValue (literalValue (atoms (popHeads n))) (stateCode t w 0 x) := by
  simp only [popHeads,atoms,List.map_append,literal_append,word_append]
  change wordValue (literalValue (atoms (popHeads n)))
    (wordValue (literalValue (atoms H)) (stateCode t (pairValue x w) d h)) = _
  rw [H_value, source_left_pair, source_right_pair]
  rfl

theorem popHeads_stack_value (xs : List V) (t x w d h : V) :
    wordValue (literalValue (atoms (popHeads (xs.length+1))))
      (stateCode t ((xs++[x]).foldr pairValue w) d h)=stateCode t w 0 x := by
  induction xs generalizing d h with
  | nil =>
      simpa only [List.nil_append,List.foldr_cons,List.foldr_nil,List.length_nil,popHeads_value_zero] using
        popHeads_value_succ 0 t x w d h
  | cons y ys ih =>
      simp only [List.length_cons,List.cons_append,List.foldr_cons]
      rw [popHeads_value_succ]
      exact ih 0 y

#print axioms popHeads_stack_value
end M6.PA.ActualCommandStepGraph
