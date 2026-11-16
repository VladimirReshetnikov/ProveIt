module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateTemplateOrdinalSyntax
@[expose] public section
/-! The unary predicate hole and literal finite ordinal-induction statement.
All formulas use the existing Foundation syntax over the template language. -/
namespace M6.PA.RelationalPredicateTemplate.Ordinal
open FFL FFL.FirstOrder

def hole : Formula 1 := .rel .predicate ![.bvar 0]
def traceProperty (p : Formula 1) (n : Nat) : Formula (n+1) :=
  Semiformula.rewAux (Rew.map (fun _ : Fin 1 => (0 : Fin (n+1))) id) p

def separationFormula (p : Formula 1) : Formula 0 :=
  ∀¹ ∃¹ ∀¹ sourceIff (mem (.bvar 1) (.bvar 0))
    (mem (.bvar 2) (.bvar 0) ⋏ traceProperty p 2)

def predicateTrace (p : Formula 1) (s c : Term n) : Formula n :=
  ∀¹ sourceIff (mem (Rew.bShift c) (.bvar 0))
    (mem (Rew.bShift s) (.bvar 0) ⋏ traceProperty p n)
def predicateTraceExists (p : Formula 1) (s : Term 0) : Formula 0 :=
  ∃¹ predicateTrace p (Rew.bShift s) (.bvar 0)

def inductionBase (p : Formula 1) : Formula 0 :=
  ∀¹ ((domain (.bvar 0) ⋏ zero (.bvar 0)) 🡒 p)
def inductionStep (p : Formula 1) : Formula 0 :=
  ∀¹ ∀¹ ((domain (.bvar 1) ⋏ (domain (.bvar 0) ⋏
    (successor (.bvar 1) (.bvar 0) ⋏
      Semiformula.rewAux (Rew.map (fun _ : Fin 1 => (1 : Fin 2)) id) p))) 🡒
      traceProperty p 1)
def inductionConclusion (p : Formula 1) : Formula 0 :=
  ∀¹ (domain (.bvar 0) 🡒 p)
def inductionStatement : Formula 0 :=
  (inductionBase hole ⋏ inductionStep hole) 🡒 inductionConclusion hole
end M6.PA.RelationalPredicateTemplate.Ordinal
