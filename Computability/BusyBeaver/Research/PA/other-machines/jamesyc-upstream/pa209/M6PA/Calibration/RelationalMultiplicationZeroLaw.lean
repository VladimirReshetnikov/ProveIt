module
public import M6PA.Theory
public import M6PA.Calibration.RelationalMultiplicationZeroLawPayload
@[expose] public section

/-! Every actual multiplication result at an empty input is an empty object.
No uniqueness of empty representatives or arithmetic graph choice is assumed. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)
attribute [local irreducible] mulPrefix
set_option maxHeartbeats 600000 in
def mulResultZeroOutput {Γ : List Form} (E : FormulaEquality Γ) (x base out : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar x)))
    (hp : ND.Proof Γ (mulResult (.fvar x) (.fvar base) (.fvar out))) :
    ND.Proof Γ (Ordinal.zero (.fvar out)) := by
  apply exsElim hp
  let body : Formula 1 := ∃¹ (Ordinal.zero (.bvar 1) ⋏
    (mulPrefix (.fvar x) (.fvar base) (.bvar 1) (.bvar 0) ⋏ edge (.bvar 0) (.fvar x) (.fvar out)))
  let C := body.free :: shifted Γ
  have hd : ND.Proof C (mulResultPayload (.fvar (x+1)) (.fvar (base+1)) (.fvar (out+1)) (.fvar 0)) := by
    have h : ND.Proof C body.free := assumption (by simp [C])
    convert h using 1 <;> (dsimp [body] <;> (try simp only [mulResultPayload]) <;> mulCompactSyntax)
  have result := mulPayloadZeroOutput (E.shifted.weaken (fun q hq => List.mem_cons_of_mem body.free hq))
    (x+1) (base+1) (out+1) 0 (up (Ordinal.zeroShift x hz) body.free) hd
  convert result using 1 <;> (dsimp [C,body] <;> mulCompactSyntax)

#print axioms mulResultZeroOutput
end M6.PA.RelationalSource.PairGraph
