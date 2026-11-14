import PA194FoundationAdditionStepExistence

/-! The existential addition-prefix predicate is closed under ordinal successor.
The original zero witness is retained, not replaced by a canonical object. -/
namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND
open Ordinal (Term Formula)

attribute [local irreducible] addPrefix

def stepWithZero {Γ : List Form} (top u base z g : Nat)
    (I : AdditionFrame Γ top u base z g) (hz : ND.Proof Γ (Ordinal.zero (.fvar z))) :
    ND.Proof Γ (addPrefixExists (.fvar u) (.fvar base)) := by
  apply exsElim (prefixStepWitness top u base z g I)
  let σ : Formula 1 := addPrefix (.fvar u) (.fvar base) (.fvar z) (.bvar 0)
  let C := σ.free :: shifted Γ
  have hp : ND.Proof C (addPrefix (.fvar (u+1)) (.fvar (base+1)) (.fvar (z+1)) (.fvar 0)) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    convert hh using 1 ; dsimp [σ]; prefixSyntax
  have out := prefixExistsIntro (u+1) (base+1) (z+1) 0 (up (Ordinal.zeroShift z hz) σ.free) hp
  convert out using 1 <;> (dsimp [C,σ] <;> prefixSyntax)


#print axioms stepWithZero
end M6.PA.RelationalSource.PairGraph
