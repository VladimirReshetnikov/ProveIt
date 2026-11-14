import PA194FoundationKuratowskiExistence
namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND

def kuratowskiDerivation (a b : Nat) :
    ND.Proof [emptyFormula, adjunctionFormula]
      (kuratowskiExists (.fvar a) (.fvar b)) :=
  kuratowskiWitness a b (assumption (by simp)) (assumption (by simp))


#print axioms kuratowskiDerivation
end M6.PA.RelationalSource.PairGraph
