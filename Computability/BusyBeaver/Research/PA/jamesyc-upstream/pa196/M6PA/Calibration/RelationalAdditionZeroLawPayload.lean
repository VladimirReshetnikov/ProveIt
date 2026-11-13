module
public import M6PA.Theory
public import M6PA.Calibration.RelationalAdditionZeroLawPrefix
public import M6PA.Calibration.RelationalAdditionStepExistence
@[expose] public section

/-! Open the displayed graph witness without identifying distinct empty objects. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)
attribute [local irreducible] addPrefix

def addResultPayload (x base out e : Term n) : Formula n :=
  ∃¹ (Ordinal.zero (Rew.bShift e) ⋏
    (addPrefix (Rew.bShift x) (Rew.bShift base) (Rew.bShift e) (.bvar 0) ⋏
      edge (.bvar 0) (Rew.bShift x) (Rew.bShift out)))

set_option maxHeartbeats 600000 in
def addPayloadZeroOutput {Γ : List Form} (E : FormulaEquality Γ) (x base out e : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar x)))
    (hp : ND.Proof Γ (addResultPayload (.fvar x) (.fvar base) (.fvar out) (.fvar e))) :
    ND.Proof Γ (eq (.fvar out) (.fvar base)) := by
  apply exsElim hp
  let body : Formula 1 := Ordinal.zero (.fvar e) ⋏
    (addPrefix (.fvar x) (.fvar base) (.fvar e) (.bvar 0) ⋏ edge (.bvar 0) (.fvar x) (.fvar out))
  let C := body.free :: shifted Γ
  have hd : ND.Proof C (Ordinal.zero (.fvar (e+1)) ⋏
      (addPrefix (.fvar (x+1)) (.fvar (base+1)) (.fvar (e+1)) (.fvar 0) ⋏
        edge (.fvar 0) (.fvar (x+1)) (.fvar (out+1)))) := by
    have h : ND.Proof C body.free := assumption (by simp [C])
    convert h using 1 <;> (dsimp [body] <;> prefixSyntax)
  have result := addPrefixZeroOutput (E.shifted.weaken (fun q hq => List.mem_cons_of_mem body.free hq))
    (x+1) (base+1) (e+1) 0 (out+1) (up (Ordinal.zeroShift x hz) body.free)
    (andLeft (andRight hd)) (andRight (andRight hd))
  convert result using 1 <;> (dsimp [C,body] <;> prefixSyntax)

#print axioms addPayloadZeroOutput
end M6.PA.RelationalSource.PairGraph
