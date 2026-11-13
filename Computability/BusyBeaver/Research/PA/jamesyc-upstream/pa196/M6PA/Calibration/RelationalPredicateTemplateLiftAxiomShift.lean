module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateTemplateLiftEquality
public import M6PA.Calibration.RelationalSourceAdjunction
@[expose] public section
namespace M6.PA.RelationalPredicateTemplate.Ordinal
open FFL FFL.FirstOrder ND

theorem transitivity_closed : RelationalSource.transitivityFormula.freeVariables=∅ := by
  simp [Finset.ext_iff,Fin.exists_fin_two,Semiformula.neg,Semiformula.freeVariables,Semiterm.freeVariables,
    RelationalSource.transitivityFormula,RelationalSource.eqAtom,RelationalSource.notEqAtom]
theorem adjunction_closed : RelationalSource.adjunctionFormula.freeVariables=∅ := by
  simp [Finset.ext_iff,Fin.exists_fin_two,Semiformula.neg,Semiformula.freeVariables,Semiterm.freeVariables,
    RelationalSource.adjunctionFormula,RelationalSource.sourceIff,RelationalSource.sourceImply,
    RelationalSource.eqAtom,RelationalSource.memAtom]
theorem intersection_closed : RelationalSource.Ordinal.intersectionFormula.freeVariables=∅ := by
  simp [Finset.ext_iff,Fin.exists_fin_two,Semiformula.neg,Semiformula.freeVariables,Semiterm.freeVariables,
    RelationalSource.Ordinal.intersectionFormula,RelationalSource.Ordinal.intersection,
    RelationalSource.sourceIff,RelationalSource.sourceImply,RelationalSource.ND.mem]

def equalityTransShift {Γ : List ND.Form}
    (h : ND.Proof Γ (liftFormula RelationalSource.transitivityFormula)) :
    ND.Proof (shifted Γ) (liftFormula RelationalSource.transitivityFormula) := by
  simpa only [lift_closed_shift _ transitivity_closed] using ND.shiftProof h

def intersectionAxiomShift {Γ : List ND.Form}
    (h : ND.Proof Γ (liftFormula RelationalSource.Ordinal.intersectionFormula)) :
    ND.Proof (shifted Γ) (liftFormula RelationalSource.Ordinal.intersectionFormula) := by
  simpa only [lift_closed_shift _ intersection_closed] using ND.shiftProof h

def inductionAdjunctionShift {Γ : List ND.Form}
    (h : ND.Proof Γ (liftFormula RelationalSource.adjunctionFormula)) :
    ND.Proof (shifted Γ) (liftFormula RelationalSource.adjunctionFormula) := by
  simpa only [lift_closed_shift _ adjunction_closed] using ND.shiftProof h

#print axioms equalityTransShift
#print axioms intersectionAxiomShift
#print axioms inductionAdjunctionShift
end M6.PA.RelationalPredicateTemplate.Ordinal
