module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateTemplateLiftAxiomShift
public import M6PA.Calibration.RelationalClosedCertificate
@[expose] public section
namespace M6.PA.RelationalClosedCertificate
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

def reflexivityNativeProof : NativeCalculus.ActualBasis.Proof
    (code reflexivityFormula (fun _=>0) 1 (ordinalReserve reflexivityFormula)) := reflexivitySupplier _ _ _
def symmetryNativeProof : NativeCalculus.ActualBasis.Proof
    (code symmetryFormula (fun _=>0) 1 (ordinalReserve symmetryFormula)) := symmetrySupplier _ _ _
def congruenceNativeProof : NativeCalculus.ActualBasis.Proof
    (code congruenceFormula (fun _=>0) 1 (ordinalReserve congruenceFormula)) :=
  congruenceSupplier _ _ _ (lt_of_lt_of_le (by decide : 1+3<8) (ordinalReserve_room _))
def transitivityNativeProof : NativeCalculus.ActualBasis.Proof
    (code transitivityFormula (fun _=>0) 1 (ordinalReserve transitivityFormula)) := transitivitySupplier _ _ _
def intersectionNativeProof : NativeCalculus.ActualBasis.Proof
    (code Ordinal.intersectionFormula (fun _=>0) 1 (ordinalReserve Ordinal.intersectionFormula)) :=
  Ordinal.intersectionAxiomSupplier _ _ _ (by decide)
    (le_trans (by decide : 1+4≤8) (ordinalReserve_room _))
def adjunctionNativeProof : NativeCalculus.ActualBasis.Proof
    (code adjunctionFormula (fun _=>0) 1 (ordinalReserve adjunctionFormula)) :=
  adjunctionSupplier _ _ _ (by decide)
    (lt_of_lt_of_le (by decide : 1+6<8) (ordinalReserve_room _)) (ordinalReserve_budget _)

#print axioms reflexivityNativeProof
#print axioms symmetryNativeProof
#print axioms congruenceNativeProof
#print axioms transitivityNativeProof
#print axioms intersectionNativeProof
#print axioms adjunctionNativeProof
end
end M6.PA.RelationalClosedCertificate

