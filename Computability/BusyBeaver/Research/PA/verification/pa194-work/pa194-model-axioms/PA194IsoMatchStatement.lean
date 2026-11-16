import PA194FoundationIsoSuccessorMatch
import PA194IsoCancelStatement
set_option maxHeartbeats 5000000
namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND
open Ordinal (Term Formula)

def isoMatchStatement : Form :=
  Ordinal.domain (.fvar 1) 🡒 Ordinal.successor (.fvar 2) (.fvar 0) 🡒
  orderIso (.fvar 0) (.fvar 1) 🡒 isoPredecessorMatch (.fvar 2) (.fvar 1)

def isoMatchStatementProof : ND.Proof isoCancelAxioms isoMatchStatement := by
  apply impIntro
  apply impIntro
  apply impIntro
  let i : Form := orderIso (.fvar 0) (.fvar 1)
  let s : Form := Ordinal.successor (.fvar 2) (.fvar 0)
  let d : Form := Ordinal.domain (.fvar 1)
  let Γ : List Form := i :: s :: d :: isoCancelAxioms
  have E : FormulaEquality Γ := ⟨⟨assumption (by simp [Γ,isoCancelAxioms,greatestImageAxioms]),
    assumption (by simp [Γ,isoCancelAxioms,greatestImageAxioms]),
    assumption (by simp [Γ,isoCancelAxioms,greatestImageAxioms])⟩,
    assumption (by simp [Γ,isoCancelAxioms,greatestImageAxioms])⟩
  have hsep : ND.Proof Γ closedStrictSeparation := assumption (by simp [Γ,isoCancelAxioms])
  have hd : ND.Proof Γ d := assumption (by simp [Γ])
  have hs : ND.Proof Γ s := assumption (by simp [Γ])
  have hi : ND.Proof Γ i := assumption (by simp [Γ])
  exact orderIsoSuccessorMatchClosed E 0 1 2 hsep hd hs hi

def isoMatchStatementDerivation : LO.FirstOrder.Derivation
    (isoCancelAxioms.map Semiformula.neg ++ [isoMatchStatement]) :=
  isoMatchStatementProof.contra (by simp)

#print axioms isoMatchStatementProof
#print axioms isoMatchStatementDerivation
end M6.PA.RelationalSource.PairGraph
