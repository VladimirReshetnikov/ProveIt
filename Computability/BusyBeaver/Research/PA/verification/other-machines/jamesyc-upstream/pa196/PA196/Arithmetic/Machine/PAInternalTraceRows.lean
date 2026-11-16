module
/- M6 PA-model runtime port. This is a fresh append-one/table adaptation;
its theorem scope is not the completed PA-unprovability endpoint. -/
public import PA196.Arithmetic.Machine.PAInternalTrace
public import PA196.Arithmetic.Machine.PAInternalRows
@[expose] public section

/-! Object-PA prefix extension specialized to every exact literal machine row.
This composes the accepted row-totality proofs with HFS trace extension. -/
namespace PA196.Arithmetic.Machine.PA.InternalTrace
open M6
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic
attribute [local irreducible] StepFormula.rowFormula StepFormula.formula Step

section Models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]

omit [V↓[ℒₒᵣ] ⊧* theory] in
lemma disjoin_of_mem (rows : List (WorkingState × Bool)) (b : Fin 6 → V)
    (p : WorkingState × Bool) (hp : p ∈ rows)
    (h : V ⊧/b (StepFormula.rowFormula p.1 p.2)) :
    V ⊧/b (StepFormula.disjoin rows) := by
  induction rows with
  | nil => simp at hp
  | cons a rows ih =>
    rcases a with ⟨q,r⟩
    simp only [StepFormula.disjoin, LogicalConnective.HomClass.map_or]
    rcases List.mem_cons.mp hp with he | ht
    · subst p; exact Or.inl h
    · exact Or.inr (ih ht)

omit [V↓[ℒₒᵣ] ⊧* theory] in
lemma row_step (src : WorkingState) (read : Bool) (b : Fin 6 → V)
    (h : V ⊧/b (StepFormula.rowFormula src read)) :
    Step (b 0) (b 1) (b 2) (b 3) (b 4) (b 5) := by
  apply (step_vector b).mp
  unfold StepFormula.formula
  apply disjoin_of_mem _ b (src,read) _ h
  cases read <;> simp [StepFormula.rows]

lemma right_row (src : WorkingState) (read : Bool) (hd : (row src read).right = true)
    (l t : V) :
    Step (src.val : V) l ((1+1)*t+read.toNat) (StepFormula.controlCode (row src read).next : V)
      ((1+1)*l+(row src read).write.toNat) t := by
  have h := consequence_iff.mp (Theory.Proof.sound (StepFormula.pa_proves_right_row src read hd)) V inferInstance
  simp only [StepFormula.rightTotalSentence,models_iff] at h
  have h' : (V ⊧/![t,l]
      (“t l. !(StepFormula.rowFormula src read) ↑src.val l ((1+1)*t+↑read.toNat)
        ↑(StepFormula.controlCode (row src read).next) ((1+1)*l+↑(row src read).write.toNat) t” : ArithmeticSemisentence 2)) := h l t
  have hr : V ⊧/![(src.val : V),l,(1+1)*t+read.toNat,
      (StepFormula.controlCode (row src read).next : V),(1+1)*l+(row src read).write.toNat,t]
      (StepFormula.rowFormula src read) := by
    rw [Semiformula.eval_substs] at h'
    apply Semiformula.Eval.of_eq h' ?_ rfl
    simp [funext_iff, Fin.forall_fin_succ, Function.comp_def, Matrix.fun_eq_vec_two, Matrix.empty_eq, numeral_eq_natCast]
  exact row_step src read _ hr

lemma left_row (src : WorkingState) (read leftBit : Bool)
    (hd : (row src read).right = false) (u t : V) :
    Step (src.val : V) ((1+1)*u+leftBit.toNat) ((1+1)*t+read.toNat)
      (StepFormula.controlCode (row src read).next : V) u
      ((1+1)*((1+1)*t+(row src read).write.toNat)+leftBit.toNat) := by
  have h := consequence_iff.mp
    (Theory.Proof.sound (StepFormula.pa_proves_left_row src read leftBit hd)) V inferInstance
  simp only [StepFormula.leftTotalSentence,models_iff] at h
  have h' : (V ⊧/![t,u]
      (“t u. !(StepFormula.rowFormula src read) ↑src.val ((1+1)*u+↑leftBit.toNat)
        ((1+1)*t+↑read.toNat) ↑(StepFormula.controlCode (row src read).next) u
        ((1+1)*((1+1)*t+↑(row src read).write.toNat)+↑leftBit.toNat)” : ArithmeticSemisentence 2)) := h u t
  have hr : V ⊧/![(src.val : V),(1+1)*u+leftBit.toNat,(1+1)*t+read.toNat,
      (StepFormula.controlCode (row src read).next : V),u,
      (1+1)*((1+1)*t+(row src read).write.toNat)+leftBit.toNat]
      (StepFormula.rowFormula src read) := by
    rw [Semiformula.eval_substs] at h'
    apply Semiformula.Eval.of_eq h' ?_ rfl
    simp [funext_iff, Fin.forall_fin_succ, Function.comp_def, Matrix.fun_eq_vec_two, Matrix.empty_eq, numeral_eq_natCast]
  exact row_step src read _ hr

end Models

def rightPrefixSentence (src : WorkingState) (read : Bool) : ArithmeticSentence :=
  let a := row src read
  “∀ n qs ls rs l t,
    !prefixFormula n qs ls rs ↑src.val l ((1+1)*t+↑read.toNat) →
    ∃ qs' ls' rs', !prefixFormula (n+1) qs' ls' rs'
      ↑(StepFormula.controlCode a.next) ((1+1)*l+↑a.write.toNat) t”

theorem pa_proves_right_extension (src : WorkingState) (read : Bool)
    (hd : (row src read).right = true) : theory ⊢ rightPrefixSentence src read := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp only [rightPrefixSentence,models_iff]
  simp [prefix_correct,numeral_eq_natCast]
  intro n qs ls rs l t h
  exact ⟨_,_,_,prefix_extend h (right_row src read hd l t)⟩

def leftPrefixSentence (src : WorkingState) (read leftBit : Bool) : ArithmeticSentence :=
  let a := row src read
  “∀ n qs ls rs u t,
    !prefixFormula n qs ls rs ↑src.val ((1+1)*u+↑leftBit.toNat) ((1+1)*t+↑read.toNat) →
    ∃ qs' ls' rs', !prefixFormula (n+1) qs' ls' rs'
      ↑(StepFormula.controlCode a.next) u ((1+1)*((1+1)*t+↑a.write.toNat)+↑leftBit.toNat)”

theorem pa_proves_left_extension (src : WorkingState) (read leftBit : Bool)
    (hd : (row src read).right = false) : theory ⊢ leftPrefixSentence src read leftBit := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp only [leftPrefixSentence,models_iff]
  simp [prefix_correct,numeral_eq_natCast]
  intro n qs ls rs u t h
  exact ⟨_,_,_,prefix_extend h (left_row src read leftBit hd u t)⟩

#print axioms pa_proves_left_extension
#print axioms pa_proves_right_extension
end PA196.Arithmetic.Machine.PA.InternalTrace

