module
public import M6PA.Theory
public import M6PA.Calibration.RelationalAdditionRestrictionPayload
@[expose] public section

/-! Genuine predecessor extraction for an arbitrary actual addition result.
Both original existential witnesses are opened capture-safely; the empty witness
is reused rather than equated with a chosen representative. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)
attribute [local irreducible] addPrefix

set_option maxHeartbeats 600000 in
def addResultPredecessor {Γ : List Form} (E : FormulaEquality Γ) (t u base out : Nat)
    (hsep : ND.Proof Γ closedInclusiveSeparation)
    (ht : ND.Proof Γ (Ordinal.domain (.fvar t)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar t) (.fvar u)))
    (hp : ND.Proof Γ (addResult (.fvar u) (.fvar base) (.fvar out))) :
    ND.Proof Γ (addPredecessorResult (.fvar t) (.fvar base) (.fvar out)) := by
  apply exsElim hp
  let body : Formula 1 := ∃¹ (Ordinal.zero (.bvar 1) ⋏
    (addPrefix (.fvar u) (.fvar base) (.bvar 1) (.bvar 0) ⋏ edge (.bvar 0) (.fvar u) (.fvar out)))
  let C := body.free :: shifted Γ
  have hd : ND.Proof C (addResultPayload (.fvar (u+1)) (.fvar (base+1)) (.fvar (out+1)) (.fvar 0)) := by
    have hh : ND.Proof C body.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [body] <;> (try simp only [addResultPayload]) <;> prefixSyntax)
  have ee := E.shifted.weaken (fun q hq => List.mem_cons_of_mem body.free hq)
  have result := restrictionResultFromPayload ee (t+1) (u+1) (base+1) (out+1) 0
    (up (additionInclusiveSeparationShift hsep) body.free)
    (up (domainShift t ht) body.free) (up (Ordinal.successorShift t u hs) body.free) hd
  convert result using 1 <;> (dsimp [C,body] <;> (try simp only [addPredecessorResult]) <;> prefixSyntax)

#print axioms addResultPredecessor
end M6.PA.RelationalSource.PairGraph
