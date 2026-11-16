module
public import M6PA.Theory
public import M6PA.Calibration.RelationalMultiplicationRestrictionWitness
@[expose] public section


namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)
attribute [local irreducible] addPrefix addResult mulPrefix
set_option maxHeartbeats 600000

def mulRestrictionResultPayload (u base out e : Term n) : Formula n :=
  ∃¹ (Ordinal.zero (Rew.bShift e) ⋏
    (mulPrefix (Rew.bShift u) (Rew.bShift base) (Rew.bShift e) (.bvar 0) ⋏
      edge (.bvar 0) (Rew.bShift u) (Rew.bShift out)))

set_option maxHeartbeats 600000 in
def mulRestrictionResultFromPayload {Γ : List Form} (E : FormulaEquality Γ)
    (t u base out e : Nat)
    (hsep : ND.Proof Γ closedInclusiveSeparation)
    (ht : ND.Proof Γ (Ordinal.domain (.fvar t)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar t) (.fvar u)))
    (hp : ND.Proof Γ (mulRestrictionResultPayload (.fvar u) (.fvar base) (.fvar out) (.fvar e))) :
    ND.Proof Γ (mulPredecessorResult (.fvar t) (.fvar base) (.fvar out)) := by
  apply exsElim hp
  let body : Formula 1 := Ordinal.zero (.fvar e) ⋏
    (mulPrefix (.fvar u) (.fvar base) (.fvar e) (.bvar 0) ⋏ edge (.bvar 0) (.fvar u) (.fvar out))
  let C := body.free :: shifted Γ
  have hd : ND.Proof C (Ordinal.zero (.fvar (e+1)) ⋏
      (mulPrefix (.fvar (u+1)) (.fvar (base+1)) (.fvar (e+1)) (.fvar 0) ⋏
        edge (.fvar 0) (.fvar (u+1)) (.fvar (out+1)))) := by
    have hh : ND.Proof C body.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [body] <;> mulCompactSyntax)
  have ee := E.shifted.weaken (fun q hq => List.mem_cons_of_mem body.free hq)
  have result := mulRestrictionResultFromGraph ee (t+1) (u+1) (base+1) (e+1) 0 (out+1)
    (up (additionInclusiveSeparationShift hsep) body.free)
    (up (domainShift t ht) body.free) (up (Ordinal.successorShift t u hs) body.free)
    (andLeft hd) (andLeft (andRight hd)) (andRight (andRight hd))
  convert result using 1 <;> (dsimp [C,body] <;> (try simp only [mulPredecessorResult,mulRestrictionResultPayload]) <;> mulCompactSyntax)

#print axioms mulRestrictionResultFromPayload
end M6.PA.RelationalSource.PairGraph
