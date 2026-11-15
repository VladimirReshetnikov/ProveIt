import PA194InverseClosedAt
set_option maxHeartbeats 8000000
namespace PA194InverseSymmetryContext
open LO LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.PairGraph
open PA194InverseClosedTemplate

def inverseSymmetryStatement (a b : Nat) : Form :=
  (Ordinal.domain (.fvar a) ⋏ orderIso (.fvar a) (.fvar b)) 🡒 orderIso (.fvar b) (.fvar a)

def inverseSymmetryAxioms : List Form :=
  [reflexivityFormula,symmetryFormula,transitivityFormula,congruenceFormula,
    emptyFormula,adjunctionFormula,Ordinal.intersectionFormula,closedInverseSeparation]

def inverseSymmetryProof (a b : Nat) :
    ND.Proof inverseSymmetryAxioms (inverseSymmetryStatement a b) := by
  apply impIntro
  let d : Form := Ordinal.domain (.fvar a) ⋏ orderIso (.fvar a) (.fvar b)
  let C := d :: inverseSymmetryAxioms
  have hd : ND.Proof C d := assumption (by simp [C])
  have E : FormulaEquality C :=
    ⟨⟨assumption (by simp [C,inverseSymmetryAxioms]),assumption (by simp [C,inverseSymmetryAxioms]),
      assumption (by simp [C,inverseSymmetryAxioms])⟩,assumption (by simp [C,inverseSymmetryAxioms])⟩
  have hs : ND.Proof C closedInverseSeparation := assumption (by simp [C,inverseSymmetryAxioms])
  exact inverseIsoSymmetry E a b (assumption (by simp [C,inverseSymmetryAxioms]))
    (assumption (by simp [C,inverseSymmetryAxioms])) (assumption (by simp [C,inverseSymmetryAxioms]))
    (inverseClosedAt a hs) (andRight hd) (andLeft hd)

def inverseSymmetryDerivation (a b : Nat) : LO.FirstOrder.Derivation
    (inverseSymmetryAxioms.map Semiformula.neg ++ [inverseSymmetryStatement a b]) :=
  (inverseSymmetryProof a b).contra (by simp)
#print axioms inverseSymmetryProof
#print axioms inverseSymmetryDerivation
end PA194InverseSymmetryContext
