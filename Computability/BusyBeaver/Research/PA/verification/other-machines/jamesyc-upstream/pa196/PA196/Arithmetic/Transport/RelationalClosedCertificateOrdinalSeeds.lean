module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateTemplateLiftAxiomShift
public import PA196.Arithmetic.Transport.RelationalClosedCertificate
public import PA196.Arithmetic.Certificates.Interface
public import PA196.Logic.Relational.SourceAdjunction
public import PA196.Logic.Relational.SourceCode
public import PA196.Logic.Relational.SourceEquality
public import PA196.Logic.Relational.SourceIntersection
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic

namespace PA196.Arithmetic.Transport.RelationalClosedCertificate
open FFL FFL.FirstOrder RelationalSource ND
noncomputable section
attribute [local irreducible] lkBudget adjunctionDerivation

def ordinalReserve (q : Form) : Nat := 8+(3+lkBudget adjunctionDerivation)+(1+Encodable.encode q)
theorem ordinalReserve_code (q : Form) : 1+Encodable.encode q≤ordinalReserve q := Nat.le_add_left _ _
theorem ordinalReserve_room (q : Form) : 8≤ordinalReserve q :=
  le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
theorem ordinalReserve_budget (q : Form) : 3+lkBudget adjunctionDerivation≤ordinalReserve q :=
  le_trans (Nat.le_add_left _ _) (Nat.le_add_right _ _)
attribute [local irreducible] ordinalReserve

theorem reflexivity_closed : reflexivityFormula.freeVariables=∅ := by
  simp [Finset.ext_iff,Fin.exists_fin_two,Semiformula.freeVariables,Semiterm.freeVariables,
    reflexivityFormula,eqAtom]
theorem symmetry_closed : symmetryFormula.freeVariables=∅ := by
  simp [Finset.ext_iff,Fin.exists_fin_two,Semiformula.freeVariables,Semiterm.freeVariables,
    symmetryFormula,eqAtom,notEqAtom]
theorem congruence_closed : congruenceFormula.freeVariables=∅ := by
  simp [Finset.ext_iff,Fin.exists_fin_two,Semiformula.freeVariables,Semiterm.freeVariables,
    congruenceFormula,eqAtom,notEqAtom,memAtom,notMemAtom]

def reflexivityNativeProof : PA196.Logic.Derivation
    (PA196.Logic.Relational.Source.code reflexivityFormula (fun _=>0) 1 (ordinalReserve reflexivityFormula)) := PA196.Logic.Relational.Source.reflexivitySupplier _ _ _
def symmetryNativeProof : PA196.Logic.Derivation
    (PA196.Logic.Relational.Source.code symmetryFormula (fun _=>0) 1 (ordinalReserve symmetryFormula)) := PA196.Logic.Relational.Source.symmetrySupplier _ _ _
def congruenceNativeProof : PA196.Logic.Derivation
    (PA196.Logic.Relational.Source.code congruenceFormula (fun _=>0) 1 (ordinalReserve congruenceFormula)) :=
  PA196.Logic.Relational.Source.congruenceSupplier _ _ _ (lt_of_lt_of_le (by decide : 1+3<8) (ordinalReserve_room _))
def transitivityNativeProof : PA196.Logic.Derivation
    (PA196.Logic.Relational.Source.code transitivityFormula (fun _=>0) 1 (ordinalReserve transitivityFormula)) := PA196.Logic.Relational.Source.transitivitySupplier _ _ _
def intersectionNativeProof : PA196.Logic.Derivation
    (PA196.Logic.Relational.Source.code Ordinal.intersectionFormula (fun _=>0) 1 (ordinalReserve Ordinal.intersectionFormula)) :=
  PA196.Logic.Relational.Source.Ordinal.intersectionAxiomSupplier _ _ _ (by decide)
    (le_trans (by decide : 1+4≤8) (ordinalReserve_room _))
def adjunctionNativeProof : PA196.Logic.Derivation
    (PA196.Logic.Relational.Source.code adjunctionFormula (fun _=>0) 1 (ordinalReserve adjunctionFormula)) :=
  PA196.Logic.Relational.Source.adjunctionSupplier _ _ _ (by decide)
    (lt_of_lt_of_le (by decide : 1+6<8) (ordinalReserve_room _)) (ordinalReserve_budget _)

#print axioms reflexivityNativeProof
#print axioms symmetryNativeProof
#print axioms congruenceNativeProof
#print axioms transitivityNativeProof
#print axioms intersectionNativeProof
#print axioms adjunctionNativeProof
end
end PA196.Arithmetic.Transport.RelationalClosedCertificate

