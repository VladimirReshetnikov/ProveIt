import PA194FoundationIdentitySuccessorWitness

/-! Successor closure of the existential identity-graph predicate. -/
namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND
open Ordinal (Term Formula)

def identityExistsStep {Γ : List Form} (E : FormulaEquality Γ) (a b : Nat)
    (hempty : ND.Proof Γ emptyFormula) (hadj : ND.Proof Γ adjunctionFormula)
    (hs : ND.Proof Γ (Ordinal.successor (.fvar a) (.fvar b)))
    (hg : ND.Proof Γ (identityExists (.fvar a))) :
    ND.Proof Γ (identityExists (.fvar b)) := by
  apply exsElim hg
  let σ : Formula 1 := identityGraph (.bvar 0) (.fvar a)
  let C := σ.free :: shifted Γ
  have hi : ND.Proof C (identityGraph (.fvar 0) (.fvar (a+1))) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [σ] <;> isoSyntax)
  let I : IdentityFrame C 0 (a+1) (b+1) := {
    equality := E.shifted.weaken (fun p hp => List.mem_cons_of_mem σ.free hp)
    empty := up (emptyClosedShift hempty) σ.free
    adjunction := up (adjunctionClosedShift hadj) σ.free
    graph := hi
    successor := up (Ordinal.successorShift a b hs) σ.free }
  have out := identityStepWitness 0 (a+1) (b+1) I
  convert out using 1 <;> (dsimp [C,σ] <;> isoSyntax)

#print axioms identityExistsStep
end M6.PA.RelationalSource.PairGraph
