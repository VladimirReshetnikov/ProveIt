module
public import M6PA.Theory
public import M6PA.Calibration.RelationalMultiplicationZeroLawPrefix
public import M6PA.Calibration.RelationalMultiplicationCompactSyntax
@[expose] public section

/-! Open the displayed graph witness without identifying distinct empty objects. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)
attribute [local irreducible] mulPrefix

def mulResultPayload (x base out e : Term n) : Formula n :=
  ∃¹ (Ordinal.zero (Rew.bShift e) ⋏
    (mulPrefix (Rew.bShift x) (Rew.bShift base) (Rew.bShift e) (.bvar 0) ⋏
      edge (.bvar 0) (Rew.bShift x) (Rew.bShift out)))

set_option maxHeartbeats 600000 in
def mulPayloadZeroOutput {Γ : List Form} (E : FormulaEquality Γ) (x base out e : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar x)))
    (hp : ND.Proof Γ (mulResultPayload (.fvar x) (.fvar base) (.fvar out) (.fvar e))) :
    ND.Proof Γ (Ordinal.zero (.fvar out)) := by
  apply exsElim hp
  let body : Formula 1 := Ordinal.zero (.fvar e) ⋏
    (mulPrefix (.fvar x) (.fvar base) (.fvar e) (.bvar 0) ⋏ edge (.bvar 0) (.fvar x) (.fvar out))
  let C := body.free :: shifted Γ
  have hd : ND.Proof C (Ordinal.zero (.fvar (e+1)) ⋏
      (mulPrefix (.fvar (x+1)) (.fvar (base+1)) (.fvar (e+1)) (.fvar 0) ⋏
        edge (.fvar 0) (.fvar (x+1)) (.fvar (out+1)))) := by
    have h : ND.Proof C body.free := assumption (by simp [C])
    convert h using 1 <;> (dsimp [body] <;> mulCompactSyntax)
  have result := mulPrefixZeroOutput (E.shifted.weaken (fun q hq => List.mem_cons_of_mem body.free hq))
    (x+1) (base+1) (e+1) 0 (out+1) (up (Ordinal.zeroShift x hz) body.free)
    (andLeft (andRight hd)) (andRight (andRight hd))
  have out := zeroTransport (E.shifted.weaken (fun q hq => List.mem_cons_of_mem body.free hq))
    (e+1) (out+1)
    ((E.shifted.weaken (fun q hq => List.mem_cons_of_mem body.free hq)).symmetryOf result) (andLeft hd)
  convert out using 1 <;> (dsimp [C,body] <;> mulCompactSyntax)

#print axioms mulPayloadZeroOutput
end M6.PA.RelationalSource.PairGraph
