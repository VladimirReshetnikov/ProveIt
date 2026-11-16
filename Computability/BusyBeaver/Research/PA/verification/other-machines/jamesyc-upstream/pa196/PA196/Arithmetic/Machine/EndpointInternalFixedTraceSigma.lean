module
public import PA196.Arithmetic.Machine.PAInternalTraceCompose
public import Foundation.FirstOrder.Arithmetic.R0.Basic
@[expose] public section
namespace PA196.Arithmetic.Machine.PA.InternalTrace.FixedTrace
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

lemma row_sigma (q : WorkingState) (b : Bool) :
    ℬ[<,ℒₒᵣ].Hierarchy 𝚺 1 (StepFormula.rowFormula q b) := by
  cases hd : (row q b).right <;> simp [StepFormula.rowFormula,hd]

lemma disjoin_sigma (rows : List (WorkingState × Bool)) :
    ℬ[<,ℒₒᵣ].Hierarchy 𝚺 1 (StepFormula.disjoin rows) := by
  induction rows with
  | nil => simp [StepFormula.disjoin]
  | cons row rows ih => simp [StepFormula.disjoin,row_sigma,ih]

lemma step_sigma : ℬ[<,ℒₒᵣ].Hierarchy 𝚺 1 StepFormula.formula :=
  disjoin_sigma StepFormula.rows

lemma segment_sigma : ℬ[<,ℒₒᵣ].Hierarchy 𝚺 1 segmentFormula := by
  simp [segmentFormula,step_sigma]

/-- Fixed endpoint arithmetic execution sentence. This is not a uniform
proof-producing procedure for arbitrary true formulas. -/
def sentence (n q l r : Nat) : ArithmeticSentence :=
  “∃ qs ls rs, !segmentFormula ↑n qs ls rs 0 0 0 ↑q ↑l ↑r”

lemma sentence_sigma (n q l r : Nat) : ℬ[<,ℒₒᵣ].Hierarchy 𝚺 1 (sentence n q l r) := by
  simp [sentence,segment_sigma]

/-- Legitimate Sigma-one completeness for a fixed closed execution sentence. -/
theorem pa_proves_fixed (n q l r : Nat)
    (h : ∃ qs ls rs : Nat, Segment n qs ls rs 0 0 0 q l r) :
    theory ⊢ sentence n q l r := by
  apply Arithmetic.sigma_one_completeness (sentence_sigma n q l r)
  simpa [sentence,models_iff,segment_correct,numeral_eq_natCast] using h
#print axioms segment_sigma
#print axioms pa_proves_fixed
end PA196.Arithmetic.Machine.PA.InternalTrace.FixedTrace

