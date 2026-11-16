module
public import PA196.Arithmetic.Scheduler.SourceCommandEncodingInternal
import PA196.Arithmetic.CommandStep
public import PA196.Arithmetic.Machine.PATheory
public import PA196.Arithmetic.CompilerHaltingWord
public import PA196.Arithmetic.Scheduler.ActualCandidateBlueprint
@[expose] public section
open PA196.Arithmetic.Machine.PA
namespace PA196.Arithmetic.Scheduler.SourceCommandEncodingInternal
open M6 M6.PA PA196.Arithmetic PA196.Arithmetic.Scheduler
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open SourceCantorInternal CommandStep
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem eval_word_pair (a b : WordExpression.Scalar) (p t d : V) :
    Scalar.eval (WordMacros.pair a b) p t d =
      pairValue (Scalar.eval a p t d) (Scalar.eval b p t d) := rfl

theorem splice_value (atom tail : V) : spliceValue atom tail =
    if decodeLeft atom=0 then pairValue 0 tail else
    if decodeLeft atom=1 then pairValue 1 (pairValue (decodeLeft (decodeRight atom)) tail) else
    pairValue (decodeLeft atom) (pairValue (decodeLeft (decodeRight atom))
      (pairValue (decodeLeft (decodeRight (decodeRight atom))) tail)) := by
  unfold spliceValue spliceExpr
  simp only [atomInput,tailInput,tag,fields]
  simp [Scalar.eval,eval_word_pair]

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
  unfold stepValue stepExpr CommandStep.shift CommandStep.mp CommandStep.ax
  simp only [CommandStep.zero,CommandStep.top,CommandStep.stack,CommandStep.cacheD,
    CommandStep.cacheH,CommandStep.tag,CommandStep.fields,CommandStep.first,CommandStep.second,
    CommandStep.state,CommandStep.pair,CommandStep.imp,CommandStep.headValue,CommandStep.push]
  have hz : decodeLeft (0:V)=0 := by simp [decodeLeft]
  by_cases h0 : decodeLeft atom=0
  · simp [commandAtom,h0,WordExpression.eval,Scalar.eval,hz,eval_source_pair]
  · by_cases h1 : decodeLeft atom=1
    · simp [commandAtom,h0,h1,WordExpression.eval,Scalar.eval,eval_source_pair]
    · simp [commandAtom,h0,h1,WordExpression.eval,Scalar.eval,eval_source_pair]
#print axioms commandAtom_step
#print axioms splice_tag
#print axioms splice_residual
#print axioms splice_atom
end PA196.Arithmetic.Scheduler.SourceCommandEncodingInternal

