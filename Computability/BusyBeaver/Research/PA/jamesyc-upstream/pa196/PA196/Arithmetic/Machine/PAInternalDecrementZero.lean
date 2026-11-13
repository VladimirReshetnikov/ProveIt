module
/- M6 PA-model runtime port. This is a fresh append-one/table adaptation;
its theorem scope is not the completed PA-unprovability endpoint. -/
public import PA196.Arithmetic.Machine.PAInternalDecrementZeroCell
public import PA196.Arithmetic.Machine.PAInternalCarryFile
public import PA196.Arithmetic.Machine.PAInternalRollbackFile
@[expose] public section
namespace PA196.Arithmetic.Machine.PA.InternalTrace.DecrementZero
open M6
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
attribute [local irreducible] Step StepFormula.formula
section Models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
/-- Uniform zero-decrement carry/rollback on an arbitrary HFS prefix and
arbitrary residual bits. The selected zero is followed by a nonempty cell;
its leading delimiter is made explicit by the low four input bits. -/
theorem segment (pre l t : V) : ∃ qs ls rs,
    Segment (2*CarryCode.cost pre+7) qs ls rs 1 l
      (CarryCode.rightFile pre (16*t+8)) 94 (l/2)
      (2*CarryCode.rightFile pre (16*t+10)+l%2) := by
  let lp := CarryCode.leftFile pre l
  obtain ⟨qa,la,ra,ha⟩ := CarryFile.segment pre l (16*t+8)
  obtain ⟨qb,lb,rb,hb⟩ := DecrementZeroCell.segment lp t
  obtain ⟨qc,lc,rc,hc⟩ := RollbackFile.segment pre l (16*t+10)
  unfold Phase at hc
  simp only [one_add_one_eq_two] at hc
  obtain ⟨q1,l1,r1,h1⟩ := segment_compose ha hb
  obtain ⟨q2,l2,r2,h2⟩ := segment_compose h1 hc
  have ht : CarryCode.cost pre+7+CarryCode.cost pre=2*CarryCode.cost pre+7 := by ring1
  exact ⟨q2,l2,r2, by simpa only [ht] using h2⟩
end Models

def sentence : ArithmeticSentence :=
  “∀ pre l t, ∃ i o c a b, !CarryCode.rightGraph i pre (16*t+8) ∧
    !CarryCode.rightGraph o pre (16*t+10) ∧ !CarryCode.costGraph c pre ∧
    !divDef a l 2 ∧ !remDef b l 2 ∧
    ∃ qs ls rs, !segmentFormula (2*c+7) qs ls rs 1 l i 94 a (2*o+b)”
theorem pa_proves_zero_decrement : theory ⊢ sentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp only [sentence,models_iff]
  simp [CarryCode.right_defined.df,CarryCode.cost_defined.df,div_defined.df,rem_defined.df,
    segment_correct,numeral_eq_natCast]
  exact segment
#print axioms segment
#print axioms pa_proves_zero_decrement
end PA196.Arithmetic.Machine.PA.InternalTrace.DecrementZero

