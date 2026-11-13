module
public import M6PA.Theory
public import M6PA.Calibration.RelationalAdditionRestrictionWitness
public import M6PA.Calibration.RelationalAdditionZeroLawPayload
@[expose] public section

namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)
attribute [local irreducible] addPrefix

set_option maxHeartbeats 600000 in
def restrictionResultFromPayload {Γ : List Form} (E : FormulaEquality Γ)
    (t u base out e : Nat)
    (hsep : ND.Proof Γ closedInclusiveSeparation)
    (ht : ND.Proof Γ (Ordinal.domain (.fvar t)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar t) (.fvar u)))
    (hp : ND.Proof Γ (addResultPayload (.fvar u) (.fvar base) (.fvar out) (.fvar e))) :
    ND.Proof Γ (addPredecessorResult (.fvar t) (.fvar base) (.fvar out)) := by
  apply exsElim hp
  let body : Formula 1 := Ordinal.zero (.fvar e) ⋏
    (addPrefix (.fvar u) (.fvar base) (.fvar e) (.bvar 0) ⋏ edge (.bvar 0) (.fvar u) (.fvar out))
  let C := body.free :: shifted Γ
  have hd : ND.Proof C (Ordinal.zero (.fvar (e+1)) ⋏
      (addPrefix (.fvar (u+1)) (.fvar (base+1)) (.fvar (e+1)) (.fvar 0) ⋏
        edge (.fvar 0) (.fvar (u+1)) (.fvar (out+1)))) := by
    have hh : ND.Proof C body.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [body] <;> prefixSyntax)
  have ee := E.shifted.weaken (fun q hq => List.mem_cons_of_mem body.free hq)
  have result := restrictionResultFromGraph ee (t+1) (u+1) (base+1) (e+1) 0 (out+1)
    (up (additionInclusiveSeparationShift hsep) body.free)
    (up (domainShift t ht) body.free) (up (Ordinal.successorShift t u hs) body.free)
    (andLeft hd) (andLeft (andRight hd)) (andRight (andRight hd))
  convert result using 1 <;> (dsimp [C,body] <;> (try simp only [addPredecessorResult]) <;> prefixSyntax)

#print axioms restrictionResultFromPayload
end M6.PA.RelationalSource.PairGraph
