import PA194FoundationIdentityInduction

/-! Actual-basis identity-graph existence on every ordinal, with all finite
ordinary source premises discharged, including exact Separation. -/
namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND

def identityStatement : Form := Ordinal.inductionConclusion identityProperty

def identityAxioms : List Form :=
  [reflexivityFormula,symmetryFormula,transitivityFormula,congruenceFormula,
    emptyFormula,adjunctionFormula,Ordinal.intersectionFormula,separationFormula (∼identityProperty)]

def identityDerivation : ND.Proof identityAxioms identityStatement :=
  identityTotalWitness
    ⟨⟨assumption (by simp [identityAxioms]),assumption (by simp [identityAxioms]),
      assumption (by simp [identityAxioms])⟩,assumption (by simp [identityAxioms])⟩
    (assumption (by simp [identityAxioms])) (assumption (by simp [identityAxioms]))
    (assumption (by simp [identityAxioms])) (assumption (by simp [identityAxioms]))


#print axioms identityDerivation
end M6.PA.RelationalSource.PairGraph
