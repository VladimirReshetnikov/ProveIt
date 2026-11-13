module
public import ExactCore
public import RowBridge
public import Foundation.FirstOrder.Arithmetic.HFS.Vec
@[expose] public section
set_option maxRecDepth 100000
namespace PalomarPA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

/-- Congruence lemma only: the separate closed NthBridge certificate must
supply the displayed exact syntax equality. -/
theorem nthAt_exact (hNth : nthFormula.toFoundation = (nthDef : ArithmeticSemisentence 3))
    (v s i : Term Empty n) :
    (nthAt v s i).toFoundation =
      Semiformula.rewAux (Rew.embSubsts ![v.toFoundation,s.toFoundation,i.toFoundation])
        (nthDef : ArithmeticSemisentence 3) := by
  rw [nthAt,Formula.to_rewrite,hNth]
  apply congrArg (fun ω => Semiformula.rewAux ω (nthDef : ArithmeticSemisentence 3))
  apply Rew.ext
  · intro j; fin_cases j <;> rfl
  · intro x; exact Empty.elim x

def standardTrace (F : ArithmeticSemisentence 6) : ArithmeticSentence :=
  “∃ n qs ls rs,
    !nthDef 0 qs 0 ∧ !nthDef 0 ls 0 ∧ !nthDef 0 rs 0 ∧
    !nthDef 215 qs n ∧
    ∀ i < n, ∃ q l r q' l' r',
      !nthDef q qs i ∧ !nthDef l ls i ∧ !nthDef r rs i ∧
      !nthDef q' qs (i+1) ∧ !nthDef l' ls (i+1) ∧ !nthDef r' rs (i+1) ∧
      !F q l r q' l' r'”

theorem traceFormula_exact (hNth : nthFormula.toFoundation = (nthDef : ArithmeticSemisentence 3))
    (step : Formula Empty 6) :
    (traceFormula step).toFoundation = standardTrace step.toFoundation := by
  have hs : Rew.bind (fun i : Fin 6 => (Semiterm.bvar (boundIndex (5-i.val)) : Semiterm ℒₒᵣ Empty 11))
      (fun x : Empty => (Empty.elim x : Semiterm ℒₒᵣ Empty 11)) =
      Rew.embSubsts ![#5,#4,#3,#2,#1,#0] := by
    apply Rew.ext
    · intro i; fin_cases i <;> rfl
    · intro x; exact Empty.elim x
  simp only [traceFormula,Formula.toFoundation,nthAt_exact hNth,Formula.to_rewrite,
    Term.to_numeral,Term.to_zero,Term.to_one,Term.to_add,Term.to_bvar]
  change _ = standardTrace step.toFoundation
  rw [show (Rew.bind (fun i : Fin 6 => (Semiterm.bvar (boundIndex (5-i.val)) : Semiterm ℒₒᵣ Empty 11))
      (fun x : Empty => (Empty.elim x : Term Empty 11).toFoundation)) =
      Rew.embSubsts ![#5,#4,#3,#2,#1,#0] from by
        trans (Rew.bind (fun i : Fin 6 => (Semiterm.bvar (boundIndex (5-i.val)) : Semiterm ℒₒᵣ Empty 11))
          (fun x : Empty => (Empty.elim x : Semiterm ℒₒᵣ Empty 11)))
        · apply Rew.ext
          · intro i; rfl
          · intro x; exact Empty.elim x
        · exact hs]
  have hsub {k m : Nat} (v : Fin k → Semiterm ℒₒᵣ Empty m) : Rew.embSubsts v = Rew.subst v := by
    apply Rew.ext
    · intro i; rfl
    · intro x; exact Empty.elim x
  simp only [hsub]
  unfold standardTrace
  simp only [Semiformula.ballLT,Semiformula.ball_eq,Semiformula.imp_eq]
  congr! 20 <;> try rfl
#print axioms traceFormula_exact
end PalomarPA
