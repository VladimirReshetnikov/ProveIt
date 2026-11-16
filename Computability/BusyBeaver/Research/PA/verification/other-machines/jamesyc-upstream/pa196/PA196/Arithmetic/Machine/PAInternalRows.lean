module
/- M6 PA-model runtime port. This is a fresh append-one/table adaptation;
its theorem scope is not the completed PA-unprovability endpoint. -/
public import PA196.Arithmetic.Machine.PAStepFormula
@[expose] public section

/-! Uniform object-PA derivations for every exact machine row. These quantify
arbitrary stack tails, not just standard natural-number witnesses. They do not
yet establish the source-calculus compiler or the internal consistency bridge. -/
namespace PA196.Arithmetic.Machine.PA.StepFormula
open M6
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic

def rightTotalSentence (src : WorkingState) (read : Bool) : ArithmeticSentence :=
  let a := row src read
  “∀ l t, !(rowFormula src read) ↑src.val l ((1+1)*t+↑read.toNat)
    ↑(controlCode a.next) ((1+1)*l+↑a.write.toNat) t”

def leftTotalSentence (src : WorkingState) (read leftBit : Bool) : ArithmeticSentence :=
  let a := row src read
  “∀ u t, !(rowFormula src read) ↑src.val ((1+1)*u+↑leftBit.toNat)
    ((1+1)*t+↑read.toNat) ↑(controlCode a.next) u
    ((1+1)*((1+1)*t+↑a.write.toNat)+↑leftBit.toNat)”

theorem pa_proves_right_row (src : WorkingState) (read : Bool)
    (hd : (row src read).right = true) : theory ⊢ rightTotalSentence src read := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp only [rightTotalSentence,models_iff]
  intro l t
  change (V ⊧/![t,l] _)
  rw [Semiformula.eval_substs]
  simp [rowFormula,hd]

theorem pa_proves_left_row (src : WorkingState) (read leftBit : Bool)
    (hd : (row src read).right = false) : theory ⊢ leftTotalSentence src read leftBit := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp only [leftTotalSentence,models_iff]
  intro u t
  change (V ⊧/![t,u] _)
  rw [Semiformula.eval_substs]
  simp [rowFormula,hd]
  refine ⟨t,u,?_⟩
  cases leftBit <;> simp

#print axioms pa_proves_right_row
#print axioms pa_proves_left_row
end PA196.Arithmetic.Machine.PA.StepFormula

