import PA194FoundationAdditionZeroLawPayload

/-! Every actual addition result at an empty input equals the base object.
No uniqueness of empty representatives or arithmetic graph choice is assumed. -/
namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND
open Ordinal (Term Formula)
attribute [local irreducible] addPrefix
set_option maxHeartbeats 600000 in
def addResultZeroOutput {Γ : List Form} (E : FormulaEquality Γ) (x base out : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar x)))
    (hp : ND.Proof Γ (addResult (.fvar x) (.fvar base) (.fvar out))) :
    ND.Proof Γ (eq (.fvar out) (.fvar base)) := by
  apply exsElim hp
  let body : Formula 1 := ∃⁰ (Ordinal.zero (.bvar 1) ⋏
    (addPrefix (.fvar x) (.fvar base) (.bvar 1) (.bvar 0) ⋏ edge (.bvar 0) (.fvar x) (.fvar out)))
  let C := body.free :: shifted Γ
  have hd : ND.Proof C (addResultPayload (.fvar (x+1)) (.fvar (base+1)) (.fvar (out+1)) (.fvar 0)) := by
    have h : ND.Proof C body.free := assumption (by simp [C])
    convert h using 1 <;> (dsimp [body] <;> (try simp only [addResultPayload]) <;> prefixSyntax)
  have result := addPayloadZeroOutput (E.shifted.weaken (fun q hq => List.mem_cons_of_mem body.free hq))
    (x+1) (base+1) (out+1) 0 (up (Ordinal.zeroShift x hz) body.free) hd
  convert result using 1 <;> (dsimp [C,body] <;> prefixSyntax)

#print axioms addResultZeroOutput
end M6.PA.RelationalSource.PairGraph
