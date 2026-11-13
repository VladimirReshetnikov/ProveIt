module
public meta import Lean
import all M6PA.Scheduler.SourceCommandEncodingInternal
import all M6PA.Scheduler.ActualCommandStepGraph
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.ActualCompilerHaltingWord
@[expose] public section
open M6.Arithmetic.PA
namespace M6.PA.SourceCommandEncodingInternal
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open SourceCantorInternal ActualCommandStepGraph
meta section
open Lean Elab Tactic in
elab "expose_source_splice_helpers" : tactic => do
  let env ← getEnv
  let names := env.constants.toList.filterMap fun (n,_) =>
    if n.toString.startsWith "M6.PA.SourceCommandEncodingInternal." &&
      ["atomInput","tailInput","tag","fields"].any (fun suffix => n.toString.endsWith ("."++suffix))
      then some (mkIdent n) else none
  let names := names.toArray
  evalTactic (← `(tactic| simp only [$[$names:ident],*]))
end
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem splice_value (atom tail : V) : spliceValue atom tail =
    if decodeLeft atom=0 then pairValue 0 tail else
    if decodeLeft atom=1 then pairValue 1 (pairValue (decodeLeft (decodeRight atom)) tail) else
    pairValue (decodeLeft atom) (pairValue (decodeLeft (decodeRight atom))
      (pairValue (decodeLeft (decodeRight (decodeRight atom))) tail)) := by
  unfold spliceValue spliceExpr
  expose_source_splice_helpers
  simp [ActualCheckExpression.eval,eval_source_pair]

noncomputable def residual (tail : V) : V :=
  if decodeLeft tail=0 then decodeRight tail else
  if decodeLeft tail=1 then decodeRight (decodeRight tail) else
  decodeRight (decodeRight (decodeRight tail))
noncomputable def commandAtom (tail : V) : V :=
  if decodeLeft tail=0 then 0 else
  if decodeLeft tail=1 then pairValue 1 (pairValue (decodeLeft (decodeRight tail)) 0) else
  pairValue (decodeLeft tail) (pairValue (decodeLeft (decodeRight tail))
    (pairValue (decodeLeft (decodeRight (decodeRight tail))) 0))

theorem splice_tag (atom tail : V) : decodeLeft (spliceValue atom tail)=decodeLeft atom := by
  rw [splice_value]
  split_ifs <;> simp_all only [source_left_pair]

theorem splice_residual (atom tail : V) : residual (spliceValue atom tail)=tail := by
  rw [splice_value]
  split_ifs <;> simp_all [residual]

theorem splice_atom (atom tail : V) : commandAtom (spliceValue atom tail)=commandAtom atom := by
  rw [splice_value]
  split_ifs <;> simp_all [commandAtom]

/-- Standalone malformed atom tails are semantically irrelevant: the exact
command evaluator reads only the dispatch tag and the required operands. -/
theorem commandAtom_step (atom state : V) :
    stepValue (commandAtom atom) state=stepValue atom state := by
  unfold stepValue stepExpr ActualCommandStepGraph.shift ActualCommandStepGraph.mp ActualCommandStepGraph.ax
  expose_pa215_step_helpers
  have hz : decodeLeft (0:V)=0 := by simp [decodeLeft]
  by_cases h0 : decodeLeft atom=0
  · simp [commandAtom,h0,ActualWordExpression.eval,ActualCheckExpression.eval,hz,eval_source_pair]
  · by_cases h1 : decodeLeft atom=1
    · simp [commandAtom,h0,h1,ActualWordExpression.eval,ActualCheckExpression.eval,eval_source_pair]
    · simp [commandAtom,h0,h1,ActualWordExpression.eval,ActualCheckExpression.eval,eval_source_pair]
#print axioms commandAtom_step
#print axioms splice_tag
#print axioms splice_residual
#print axioms splice_atom
end M6.PA.SourceCommandEncodingInternal

