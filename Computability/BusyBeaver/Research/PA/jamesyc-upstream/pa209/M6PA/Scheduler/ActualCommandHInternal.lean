module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.ActualCommandShiftInternal
@[expose] public section
open M6.Arithmetic.PA
namespace M6.PA.ActualCommandStepGraph
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open SourceCantorInternal ActualCommandWordGraph ActualCommandLiteralInternal
open M6.Source M6.Source.CommandAtomEncoding M6.Source.ActualCommandMacros
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem literal_H_word : literalValue (V := V) (atoms H)=axThenShifts (0 : V) 0 0 11 := by
  simp only [H,D,atoms,List.map_append,List.map_cons,List.map_nil,List.map_replicate,
    List.cons_append,List.nil_append,literal_cons,literal_nil,ax_atom_numeral,Nat.cast_zero,axThenShifts]
  rfl

/-- The actual fixed H word uniformly pops W and preserves arbitrary T,
including T=1 and the Cantor zero alias. No cleanliness premise is needed. -/
theorem H_value (t w d h : V) :
    wordValue (literalValue (atoms H)) (stateCode t w d h)=
      stateCode t (decodeRight w) 0 (decodeLeft w) := by
  rw [literal_H_word,ax_shift11_value]

theorem H_expr_value (p a b t w d h : V) :
    wordValue (ActualWordExpression.eval (ActualWordMacros.literal (atoms H)) p a b)
      (stateCode t w d h)=stateCode t (decodeRight w) 0 (decodeLeft w) := by
  rw [literal_expr,H_value]

#print axioms H_value
#print axioms H_expr_value
end M6.PA.ActualCommandStepGraph
