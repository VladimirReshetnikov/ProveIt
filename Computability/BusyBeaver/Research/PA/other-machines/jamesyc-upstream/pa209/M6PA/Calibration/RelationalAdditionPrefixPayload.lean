module
public import M6PA.Theory
public import M6PA.Calibration.RelationalAdditionGivenZero
@[expose] public section
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)
attribute [local irreducible] addPrefix

def prefixPayload (top base z : Term n) : Formula n :=
  ∃¹ (Ordinal.zero (Rew.bShift z) ⋏ addPrefix (Rew.bShift top) (Rew.bShift base) (Rew.bShift z) (.bvar 0))

set_option maxHeartbeats 600000 in
def payloadZero {Γ : List Form} (top base z : Nat)
    (hp : ND.Proof Γ (prefixPayload (.fvar top) (.fvar base) (.fvar z))) :
    ND.Proof Γ (Ordinal.zero (.fvar z)) := by
  apply exsElim hp
  let τ : Formula 1 := Ordinal.zero (.fvar z) ⋏ addPrefix (.fvar top) (.fvar base) (.fvar z) (.bvar 0)
  have hd : ND.Proof (τ.free :: shifted Γ) (Ordinal.zero (.fvar (z+1)) ⋏
      addPrefix (.fvar (top+1)) (.fvar (base+1)) (.fvar (z+1)) (.fvar 0)) := by
    have hh : ND.Proof (τ.free :: shifted Γ) τ.free := assumption (by simp)
    convert hh using 1 ; dsimp [τ]; prefixSyntax
  convert andLeft hd using 1 <;> (dsimp [τ] <;> prefixSyntax)

set_option maxHeartbeats 600000 in
def payloadGraph {Γ : List Form} (top base z : Nat)
    (hp : ND.Proof Γ (prefixPayload (.fvar top) (.fvar base) (.fvar z))) :
    ND.Proof Γ (prefixGraphExists (.fvar top) (.fvar base) (.fvar z)) := by
  apply exsElim hp
  let τ : Formula 1 := Ordinal.zero (.fvar z) ⋏ addPrefix (.fvar top) (.fvar base) (.fvar z) (.bvar 0)
  have hd : ND.Proof (τ.free :: shifted Γ) (Ordinal.zero (.fvar (z+1)) ⋏
      addPrefix (.fvar (top+1)) (.fvar (base+1)) (.fvar (z+1)) (.fvar 0)) := by
    have hh : ND.Proof (τ.free :: shifted Γ) τ.free := assumption (by simp)
    convert hh using 1 ; dsimp [τ]; prefixSyntax
  have hi : ND.Proof (τ.free :: shifted Γ)
      ((addPrefix (.fvar (top+1)) (.fvar (base+1)) (.fvar (z+1)) (.bvar 0))/[.fvar 0]) := by
    convert andRight hd using 1 <;> prefixSyntax
  have out := exsIntro (addPrefix (.fvar (top+1)) (.fvar (base+1)) (.fvar (z+1)) (.bvar 0)) (.fvar 0) hi
  convert out using 1 <;> (dsimp [τ] <;> prefixSyntax)

#print axioms payloadZero
#print axioms payloadGraph
end M6.PA.RelationalSource.PairGraph
