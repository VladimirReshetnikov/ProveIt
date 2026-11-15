import PA194ForwardSuccVariable
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace M6.PA.RelationalSource
open LO LO.FirstOrder ND
open Ordinal (Term Formula)
open M6.PA.RelationalSource.PairGraph

def successorValueEqualityAxioms : List Form :=
  [reflexivityFormula, symmetryFormula, congruenceFormula, transitivityFormula]

def successorValueNormalizationStatement : Form :=
  sourceIff (successorVariableValue 0 1)
    (Ordinal.domain (.fvar 0) ⋏ (Ordinal.domain (.fvar 1) ⋏ Ordinal.successor (.fvar 0) (.fvar 1)))

def successorValueNormalizationProof : ND.Proof successorValueEqualityAxioms successorValueNormalizationStatement := by
  unfold successorValueNormalizationStatement sourceIff sourceImply
  apply andIntro
  · apply impIntro
    let C : List Form := successorVariableValue 0 1 :: successorValueEqualityAxioms
    have E : FormulaEquality C := ⟨⟨assumption (by simp [C,successorValueEqualityAxioms]),
      assumption (by simp [C,successorValueEqualityAxioms]),
      assumption (by simp [C,successorValueEqualityAxioms])⟩,
      assumption (by simp [C,successorValueEqualityAxioms])⟩
    exact successorVariableValue_forward E 0 1 (assumption (by simp [C]))
  · apply impIntro
    let q : Form := Ordinal.domain (.fvar 0) ⋏ (Ordinal.domain (.fvar 1) ⋏ Ordinal.successor (.fvar 0) (.fvar 1))
    let C : List Form := q :: successorValueEqualityAxioms
    have E : FormulaEquality C := ⟨⟨assumption (by simp [C,successorValueEqualityAxioms]),
      assumption (by simp [C,successorValueEqualityAxioms]),
      assumption (by simp [C,successorValueEqualityAxioms])⟩,
      assumption (by simp [C,successorValueEqualityAxioms])⟩
    exact successorVariableValue_backward E 0 1 (assumption (by simp [C,q]))

def successorValueNormalizationDerivation : LO.FirstOrder.Derivation
    (successorValueEqualityAxioms.map Semiformula.neg ++ [successorValueNormalizationStatement]) :=
  successorValueNormalizationProof.contra (by simp [ND.Proof])

#print axioms successorValueNormalizationProof
#print axioms successorValueNormalizationDerivation
end M6.PA.RelationalSource
