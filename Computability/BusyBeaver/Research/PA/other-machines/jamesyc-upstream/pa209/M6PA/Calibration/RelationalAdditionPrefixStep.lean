module
public import M6PA.Theory
public import M6PA.Calibration.RelationalAdditionPrefixPayload
@[expose] public section
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)
attribute [local irreducible] addPrefix
set_option maxHeartbeats 600000 in
def prefixExistsStep {Γ : List Form} (S : SetProofs Γ) (top u base : Nat)
    (ht : ND.Proof Γ (Ordinal.domain (.fvar top)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar top) (.fvar u)))
    (hp : ND.Proof Γ (addPrefixExists (.fvar top) (.fvar base))) :
    ND.Proof Γ (addPrefixExists (.fvar u) (.fvar base)) := by
  apply exsElim hp
  let σ : Formula 1 := ∃¹ (Ordinal.zero (.bvar 1) ⋏
    addPrefix (.fvar top) (.fvar base) (.bvar 1) (.bvar 0))
  let C := σ.free :: shifted Γ
  have hx : ND.Proof C (prefixPayload (.fvar (top+1)) (.fvar (base+1)) (.fvar 0)) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    convert hh using 1 ; dsimp [σ]; simp only [prefixPayload]; prefixSyntax
  have ss := S.shift.weaken (fun q hq => List.mem_cons_of_mem σ.free hq)
  have out := prefixGivenZero ss (top+1) (u+1) (base+1) 0
    (up (domainShift top ht) σ.free) (up (Ordinal.successorShift top u hs) σ.free)
    (payloadZero _ _ _ hx) (payloadGraph _ _ _ hx)
  convert out using 1 <;> (dsimp [C,σ] <;> prefixSyntax)
#print axioms prefixExistsStep
end M6.PA.RelationalSource.PairGraph
