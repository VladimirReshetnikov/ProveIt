import PA194FoundationAdditionStepWithZero
namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND
open Ordinal (Term Formula)
attribute [local irreducible] addPrefix
set_option maxHeartbeats 600000 in
def prefixGivenZero {Γ : List Form} (S : SetProofs Γ) (top u base z : Nat)
    (ht : ND.Proof Γ (Ordinal.domain (.fvar top)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar top) (.fvar u)))
    (hz : ND.Proof Γ (Ordinal.zero (.fvar z)))
    (hp : ND.Proof Γ (prefixGraphExists (.fvar top) (.fvar base) (.fvar z))) :
    ND.Proof Γ (addPrefixExists (.fvar u) (.fvar base)) := by
  apply exsElim hp
  let σ : Formula 1 := addPrefix (.fvar top) (.fvar base) (.fvar z) (.bvar 0)
  let C := σ.free :: shifted Γ
  have hd : ND.Proof C (addPrefix (.fvar (top+1)) (.fvar (base+1)) (.fvar (z+1)) (.fvar 0)) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    convert hh using 1 ; dsimp [σ]; prefixSyntax
  have St := S.shift.weaken (fun q hq => List.mem_cons_of_mem σ.free hq)
  let I : AdditionFrame C (top+1) (u+1) (base+1) (z+1) 0 :=
    ⟨St,up (domainShift top ht) σ.free,up (Ordinal.successorShift top u hs) σ.free,hd⟩
  have out := stepWithZero (top+1) (u+1) (base+1) (z+1) 0 I (up (Ordinal.zeroShift z hz) σ.free)
  convert out using 1 <;> (dsimp [C,σ] <;> prefixSyntax)


#print axioms prefixGivenZero
end M6.PA.RelationalSource.PairGraph
