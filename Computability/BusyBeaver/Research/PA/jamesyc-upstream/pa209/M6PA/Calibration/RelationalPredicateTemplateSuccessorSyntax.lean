module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateTemplateOrdinalRewriting
public import M6PA.Calibration.RelationalPredicateTemplateLiftLogic
@[expose] public section

/-! A single unary-hole successor totality template. Source syntax is closed;
the target predicate may retain arbitrary parameters when interpreted. -/
namespace M6.PA.RelationalPredicateTemplate.Successor
open FFL FFL.FirstOrder ND Ordinal

def pred (t : Term n) : Formula n := .rel .predicate ![t]
def inputBody : Formula 1 := domain (.bvar 0) ⋏ pred (.bvar 0)
def input : Formula 0 := ∃¹ inputBody
def outputBody : Formula 1 := domain (.bvar 0) ⋏
  (∃¹ (pred (.bvar 0) ⋏ successor (.bvar 0) (.bvar 1)))
def output : Formula 0 := ∃¹ outputBody
def closureBody : Formula 1 := domain (.bvar 0) 🡒
  ∃¹ (domain (.bvar 0) ⋏ successor (.bvar 1) (.bvar 0))
def closure : Formula 0 := ∀¹ closureBody
def statement : Formula 0 := input 🡒 output

macro "finishSuccessorSyntax" : tactic => `(tactic|
  repeat' first
    | rfl
    | (funext i; fin_cases i <;> rfl)
    | (change Semiformula.and _ _ = Semiformula.and _ _; congr 1)
    | (change Semiformula.or _ _ = Semiformula.or _ _; congr 1)
    | (change Semiformula.all _ = Semiformula.all _; congr 1)
    | (change Semiformula.exs _ = Semiformula.exs _; congr 1)
    | (change Semiformula.rel _ _ = Semiformula.rel _ _; congr 1)
    | (change Semiformula.nrel _ _ = Semiformula.nrel _ _; congr 1))

macro "successorTemplateSyntax" : tactic => `(tactic|
  (simp only [statement,input,inputBody,output,outputBody,closure,closureBody,pred,
    zero,subset,transitive,memberTransitive,memberLinear,nonempty,
    least,greatest,internalExtrema,representative,memberIr,domain,inhabited,mem,eq,
    successor,sourceIff,Semiformula.shift,Semiformula.free,
    Rewriting.shift,Rewriting.free,Rewriting.subst,app_eq_rewAux,
    Semiformula.rewAux,Semiformula.neg,Semiformula.imp_eq,Semiformula.neg_eq];
   finishSuccessorSyntax))

theorem input_closed : input.freeVariables=∅ := by
  apply Semiformula.freeVariables_eq_empty_of_shift_eq
  change input.shift=input
  successorTemplateSyntax

theorem output_closed : output.freeVariables=∅ := by
  apply Semiformula.freeVariables_eq_empty_of_shift_eq
  change output.shift=output
  successorTemplateSyntax

theorem closure_closed : closure.freeVariables=∅ := by
  apply Semiformula.freeVariables_eq_empty_of_shift_eq
  change closure.shift=closure
  successorTemplateSyntax

theorem statement_closed : statement.freeVariables=∅ := by
  simp [statement,input_closed,output_closed]

#print axioms statement_closed
#print axioms closure_closed
end M6.PA.RelationalPredicateTemplate.Successor
