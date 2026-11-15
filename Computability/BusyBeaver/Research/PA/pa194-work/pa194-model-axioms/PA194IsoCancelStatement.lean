import PA194FoundationIsoCancelClosed
import PA194OrderIsoGreatestStatement
set_option maxHeartbeats 5000000
namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND
open Ordinal (Term Formula)

def isoCancelAxioms : List Form := closedStrictSeparation :: greatestImageAxioms

def isoCancelStatement : Form :=
  Ordinal.domain (.fvar 1) 🡒 Ordinal.successor (.fvar 2) (.fvar 0) 🡒
  Ordinal.successor (.fvar 3) (.fvar 1) 🡒 orderIso (.fvar 0) (.fvar 1) 🡒
  orderIso (.fvar 2) (.fvar 3)

def isoCancelStatementProof : ND.Proof isoCancelAxioms isoCancelStatement := by
  apply impIntro
  apply impIntro
  apply impIntro
  apply impIntro
  let i : Form := orderIso (.fvar 0) (.fvar 1)
  let sq : Form := Ordinal.successor (.fvar 3) (.fvar 1)
  let sp : Form := Ordinal.successor (.fvar 2) (.fvar 0)
  let d : Form := Ordinal.domain (.fvar 1)
  let Γ : List Form := i :: sq :: sp :: d :: isoCancelAxioms
  have E : FormulaEquality Γ := ⟨⟨assumption (by simp [Γ,isoCancelAxioms,greatestImageAxioms]),
    assumption (by simp [Γ,isoCancelAxioms,greatestImageAxioms]),
    assumption (by simp [Γ,isoCancelAxioms,greatestImageAxioms])⟩,
    assumption (by simp [Γ,isoCancelAxioms,greatestImageAxioms])⟩
  have hsep : ND.Proof Γ closedStrictSeparation := assumption (by simp [Γ,isoCancelAxioms])
  have hd : ND.Proof Γ d := assumption (by simp [Γ])
  have hp : ND.Proof Γ sp := assumption (by simp [Γ])
  have hq : ND.Proof Γ sq := assumption (by simp [Γ])
  have hi : ND.Proof Γ i := assumption (by simp [Γ])
  exact orderIsoSuccessorCancelClosed E 0 1 2 3 hsep hd hp hq hi

def isoCancelStatementDerivation : LO.FirstOrder.Derivation
    (isoCancelAxioms.map Semiformula.neg ++ [isoCancelStatement]) :=
  isoCancelStatementProof.contra (by simp)

#print axioms isoCancelStatementProof
#print axioms isoCancelStatementDerivation
end M6.PA.RelationalSource.PairGraph
