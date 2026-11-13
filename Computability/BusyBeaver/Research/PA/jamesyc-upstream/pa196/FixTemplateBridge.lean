module
public import FixTemplateCore
public import RowBridge
@[expose] public section
namespace PalomarPA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

theorem substClosed_to (p : Formula Empty k) (v : Fin k → Term Empty n) :
 (substClosed p v).toFoundation =
 Semiformula.rewAux (Rew.subst (fun i => (v i).toFoundation)) p.toFoundation := by
 rw [substClosed,Formula.to_rewrite]
 congr 1
 apply Rew.ext
 · intro i; rfl
 · intro x; exact Empty.elim x

theorem substClosed_to2 (p : Formula Empty 2) (a b : Term Empty n) :
 (substClosed p (fun j => if j.val=0 then a else b)).toFoundation =
 p.toFoundation/[a.toFoundation,b.toFoundation] := by
 rw [substClosed_to]
 congr 1
 apply Rew.ext
 · intro i; fin_cases i <;> rfl
 · intro x; exact Empty.elim x

def standardFixSucc (mem cs cp : ArithmeticSemisentence 2) : ArithmeticSemisentence 3 :=
 “u ih s. ∀ x < u + (s+1),
   (!mem x u → x ≤ s ∧ !cs x ih) ∧
   (x ≤ s ∧ !cp x ih → !mem x u)”

theorem fixSuccTemplate_to (mem cs cp : Formula Empty 2) :
 (fixSuccTemplate mem cs cp).toFoundation =
 standardFixSucc mem.toFoundation cs.toFoundation cp.toFoundation := by
 simp only [fixSuccTemplate,Formula.toFoundation,Formula.to_neg,substClosed_to2,
  Term.to_add,Term.to_one,Term.to_bvar]
 unfold standardFixSucc
 simp only [Semiformula.ballLT,Semiformula.ball_eq,Semiformula.imp_eq, Semiformula.Operator.LE.def_of_Eq_of_LT, le_eq]
 congr! 20
 all_goals first | rfl | (change Semiformula.nrel (L := ℒₒᵣ) Language.ORing.Rel.lt _ = Semiformula.nrel (L := ℒₒᵣ) Language.ORing.Rel.lt _; congr 1; funext i; fin_cases i <;> simp [Rew.bShift,boundIndex])
def standardFixPoint (mem result : ArithmeticSemisentence 2) : ArithmeticSemisentence 1 :=
 “x. ∃ s L, !result L s ∧ !mem x L”
theorem fixPointTemplate_to (mem result : Formula Empty 2) :
 (fixPointTemplate mem result).toFoundation =
 standardFixPoint mem.toFoundation result.toFoundation := by
 simp only [fixPointTemplate,Formula.toFoundation,substClosed_to2,Term.to_bvar]
 rfl

def standardNth (pair3 : ArithmeticSemisentence 4) (graph : ArithmeticSemisentence 1) :
 ArithmeticSemisentence 3 := “y v i. ∃ pr, !pair3 pr v i y ∧ !graph pr”
theorem nthTemplate_to (pair3 : Formula Empty 4) (graph : Formula Empty 1) :
 (nthTemplate pair3 graph).toFoundation = standardNth pair3.toFoundation graph.toFoundation := by
 simp only [nthTemplate,Formula.toFoundation,substClosed_to,Term.to_bvar]
 unfold standardNth
 congr 3
 all_goals
  apply Rew.ext
  · intro i; fin_cases i <;> rfl
  · intro x; exact Empty.elim x
#print axioms fixSuccTemplate_to
#print axioms fixPointTemplate_to
#print axioms nthTemplate_to
end PalomarPA
