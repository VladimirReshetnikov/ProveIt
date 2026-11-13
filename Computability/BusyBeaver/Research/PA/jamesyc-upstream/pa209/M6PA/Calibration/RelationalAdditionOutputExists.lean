module
public import M6PA.Theory
public import M6PA.Calibration.RelationalAdditionOutputPayload
@[expose] public section

/-! The exact addition-prefix existential entails an ordinal addition result. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)
attribute [local irreducible] addPrefix

set_option maxHeartbeats 600000 in
def addOutputFromExists {Γ : List Form} (E : FormulaEquality Γ) (x y : Nat)
    (hp : ND.Proof Γ (addPrefixExists (.fvar x) (.fvar y))) :
    ND.Proof Γ (addOutput (.fvar x) (.fvar y)) := by
  apply exsElim hp
  let σ : Formula 1 := ∃¹ (Ordinal.zero (.bvar 1) ⋏ addPrefix (.fvar x) (.fvar y) (.bvar 1) (.bvar 0))
  let C := σ.free :: shifted Γ
  have hd : ND.Proof C (prefixPayload (.fvar (x+1)) (.fvar (y+1)) (.fvar 0)) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [σ] <;> (try simp only [prefixPayload]) <;> prefixSyntax)
  have out := addOutputFromPayload (E.shifted.weaken (fun p h => List.mem_cons_of_mem σ.free h)) (x+1) (y+1) 0 hd
  convert out using 1 <;> (dsimp [C,σ] <;> (try simp only [addOutput]) <;> prefixSyntax)

#print axioms addOutputFromExists
end M6.PA.RelationalSource.PairGraph

