module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateTemplateOrdinalInduction
@[expose] public section
/-! A single concrete finite host LK template, with one unary relation symbol.
Its seven explicit assumptions are retained for native certificate discharge. -/
namespace M6.PA.RelationalPredicateTemplate.Ordinal
open FFL FFL.FirstOrder ND

def inductionAxioms : List Form :=
  [liftFormula RelationalSource.reflexivityFormula,
   liftFormula RelationalSource.symmetryFormula,
   liftFormula RelationalSource.congruenceFormula,
   liftFormula RelationalSource.transitivityFormula,
   liftFormula RelationalSource.Ordinal.intersectionFormula,
   liftFormula RelationalSource.adjunctionFormula,
   separationFormula (∼hole)]

def inductionDerivation : ND.Proof inductionAxioms inductionStatement := by
  apply impIntro
  have he : EqualityProofs ((inductionBase hole ⋏ inductionStep hole)::inductionAxioms) :=
    ⟨assumption (by simp [inductionAxioms]),assumption (by simp [inductionAxioms]),
      assumption (by simp [inductionAxioms])⟩
  exact uniformInduction he hole
    (assumption (by simp [inductionAxioms]))
    (assumption (by simp [inductionAxioms]))
    (assumption (by simp [inductionAxioms]))
    (assumption (by simp [inductionAxioms]))
    (andLeft (assumption (p:=inductionBase hole ⋏ inductionStep hole) (by simp)))
    (andRight (assumption (p:=inductionBase hole ⋏ inductionStep hole) (by simp)))

#print axioms inductionDerivation
end M6.PA.RelationalPredicateTemplate.Ordinal
