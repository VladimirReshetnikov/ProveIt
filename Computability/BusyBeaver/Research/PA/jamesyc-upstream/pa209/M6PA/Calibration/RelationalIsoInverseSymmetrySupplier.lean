module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoInverseSymmetry
@[expose] public section

/-! Actual-basis existential symmetry: the universally closed graph-parameter
Separation axiom is supplied explicitly, with its fresh-label budget. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def inverseSymmetryStatement (a b : Nat) : Form :=
  (Ordinal.domain (.fvar a) ⋏ orderIso (.fvar a) (.fvar b)) 🡒 orderIso (.fvar b) (.fvar a)

def inverseSymmetryAxioms (a : Nat) : List Form :=
  [reflexivityFormula,symmetryFormula,transitivityFormula,congruenceFormula,
    emptyFormula,adjunctionFormula,Ordinal.intersectionFormula,inverseClosedSeparation a]

def inverseSymmetryDerivation (a b : Nat) :
    ND.Proof (inverseSymmetryAxioms a) (inverseSymmetryStatement a b) := by
  apply impIntro
  let d : Form := Ordinal.domain (.fvar a) ⋏ orderIso (.fvar a) (.fvar b)
  let C := d :: inverseSymmetryAxioms a
  have hd : ND.Proof C d := assumption (by simp [C])
  have E : FormulaEquality C :=
    ⟨⟨assumption (by simp [C,inverseSymmetryAxioms]),assumption (by simp [C,inverseSymmetryAxioms]),
      assumption (by simp [C,inverseSymmetryAxioms])⟩,assumption (by simp [C,inverseSymmetryAxioms])⟩
  exact inverseIsoSymmetry E a b (assumption (by simp [C,inverseSymmetryAxioms]))
    (assumption (by simp [C,inverseSymmetryAxioms])) (assumption (by simp [C,inverseSymmetryAxioms]))
    (assumption (by simp [C,inverseSymmetryAxioms])) (andRight hd) (andLeft hd)

def inverseSymmetryAxiomSupplier (a : Nat) (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i, f i < lo) (hz : lo+6 < z)
    (hsep : lo+4+depth (∼inverseProperty 0 (a+1)) ≤ z)
    (hadj : lo+2+lkBudget adjunctionDerivation ≤ z)
    (p : Form) (hp : p ∈ inverseSymmetryAxioms a) : NativeCalculus.ActualBasis.Proof (code p f lo z) := by
  classical
  by_cases h0 : p = reflexivityFormula
  · subst p; exact reflexivitySupplier f lo z
  by_cases h1 : p = symmetryFormula
  · subst p; exact symmetrySupplier f lo z
  by_cases h2 : p = transitivityFormula
  · subst p; exact transitivitySupplier f lo z
  by_cases h3 : p = congruenceFormula
  · subst p; exact congruenceSupplier f lo z (by omega)
  by_cases h4 : p = emptyFormula
  · subst p; exact emptySupplier f lo z (by omega)
  by_cases h5 : p = adjunctionFormula
  · subst p; exact adjunctionSupplier f lo z hlo hz hadj
  by_cases h6 : p = Ordinal.intersectionFormula
  · subst p; exact Ordinal.intersectionAxiomSupplier f lo z hlo (by omega)
  have h7 : p = inverseClosedSeparation a := by
    simpa [inverseSymmetryAxioms,h0,h1,h2,h3,h4,h5,h6] using hp
  subst p; exact closedSeparationSupplier _ f lo z hlo hf hsep

def inverseSymmetrySupplier (a b : Nat) (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i, f i < lo) (hz : lo+6 < z)
    (hsep : lo+4+depth (∼inverseProperty 0 (a+1)) ≤ z)
    (hadj : lo+2+lkBudget adjunctionDerivation ≤ z)
    (hbudget : lo+lkBudget (inverseSymmetryDerivation a b) ≤ z) :
    NativeCalculus.ActualBasis.Proof (code (inverseSymmetryStatement a b) f lo z) :=
  compileContext (inverseSymmetryAxioms a) _ (inverseSymmetryDerivation a b) f lo z hlo hf hbudget
    (inverseSymmetryAxiomSupplier a f lo z hlo hf hz hsep hadj)

#print axioms inverseSymmetryDerivation
#print axioms inverseSymmetryAxiomSupplier
#print axioms inverseSymmetrySupplier
end M6.PA.RelationalSource.PairGraph
