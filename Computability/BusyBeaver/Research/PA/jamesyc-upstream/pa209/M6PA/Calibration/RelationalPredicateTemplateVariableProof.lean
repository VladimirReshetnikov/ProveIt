module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateTemplateLiftEquality
public import M6PA.Calibration.RelationalPredicateTemplateOrdinalRewriting
@[expose] public section

/-! A finite template proof of variable-value existence, using only actual
ordinary equality reflexivity. The source variable remains a parameter. -/
namespace M6.PA.RelationalPredicateTemplate.Variable
open FFL FFL.FirstOrder ND Ordinal

def input : Formula 0 := domain (.fvar 0)
def outputBody : Formula 1 := domain (.bvar 0) ⋏ eq (.bvar 0) (.fvar 0)
def output : Formula 0 := ∃¹ outputBody
def statement : Formula 0 := input 🡒 output
def reflexivity : Formula 0 := liftFormula RelationalSource.reflexivityFormula

macro "variableTemplateSyntax" : tactic => `(tactic|
  (simp only [input,outputBody,output,statement,reflexivity,liftFormula,
    RelationalSource.reflexivityFormula,RelationalSource.eqAtom,
    Semiformula.lMap,injection,zero,subset,transitive,memberTransitive,memberLinear,
    nonempty,least,greatest,internalExtrema,representative,memberIr,domain,mem,eq,
    Semiformula.shift,Semiformula.free,Rewriting.shift,Rewriting.free,Rewriting.subst,
    app_eq_rewAux,Semiformula.rewAux,Semiformula.neg,Semiformula.imp_eq,Semiformula.neg_eq];
    repeat' first | rfl | (funext i; fin_cases i <;> rfl) | congr 1))

def derivation : ND.Proof [reflexivity] statement := by
  apply impIntro
  have hd : ND.Proof [input,reflexivity] input := assumption (by simp)
  have hr : ND.Proof [input,reflexivity] (eq (.fvar 0) (.fvar 0)) := by
    have h : ND.Proof [input,reflexivity] (∀¹ eq (.bvar 0) (.bvar 0)) := by
      convert (assumption (Γ:=[input,reflexivity]) (p:=reflexivity) (by simp)) using 1
      variableTemplateSyntax
    convert allElim (eq (.bvar 0) (.bvar 0)) (.fvar 0) h using 1
    variableTemplateSyntax
  apply exsIntro outputBody (.fvar 0)
  convert andIntro hd hr using 1
  variableTemplateSyntax

#print axioms derivation
end M6.PA.RelationalPredicateTemplate.Variable
