module
public import M6PA.Theory
public import M6PA.Calibration.RelationalAdditionOutputPrefix
@[expose] public section

/-! Eliminate the original graph witness while retaining the same zero. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)
attribute [local irreducible] addPrefix

set_option maxHeartbeats 600000 in
def addOutputFromPayload {Γ : List Form} (E : FormulaEquality Γ) (x y z : Nat)
    (hp : ND.Proof Γ (prefixPayload (.fvar x) (.fvar y) (.fvar z))) :
    ND.Proof Γ (addOutput (.fvar x) (.fvar y)) := by
  have hz := payloadZero x y z hp
  apply exsElim (payloadGraph x y z hp)
  let σ : Formula 1 := addPrefix (.fvar x) (.fvar y) (.fvar z) (.bvar 0)
  let C := σ.free :: shifted Γ
  have hd : ND.Proof C (addPrefix (.fvar (x+1)) (.fvar (y+1)) (.fvar (z+1)) (.fvar 0)) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [σ] <;> prefixSyntax)
  have ee := E.shifted.weaken (fun p h => List.mem_cons_of_mem σ.free h)
  have out := addOutputFromPrefix ee (x+1) (y+1) (z+1) 0 (up (Ordinal.zeroShift z hz) σ.free) hd
  convert out using 1 <;> (dsimp [C,σ] <;> (try simp only [addOutput]) <;> prefixSyntax)

#print axioms addOutputFromPayload
end M6.PA.RelationalSource.PairGraph

