module
public import M6PA.Theory
public import M6PA.Calibration.RelationalMultiplicationRestrictionPayload
@[expose] public section

/-! Genuine predecessor extraction for an arbitrary actual multiplication result.
Both original existential witnesses are opened capture-safely; the empty witness
is reused rather than equated with a chosen representative. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)
attribute [local irreducible] addPrefix addResult mulPrefix
set_option maxHeartbeats 600000

set_option maxHeartbeats 600000 in
def mulResultPredecessor {Γ : List Form} (E : FormulaEquality Γ) (t u base out : Nat)
    (hsep : ND.Proof Γ closedInclusiveSeparation)
    (ht : ND.Proof Γ (Ordinal.domain (.fvar t)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar t) (.fvar u)))
    (hp : ND.Proof Γ (mulResult (.fvar u) (.fvar base) (.fvar out))) :
    ND.Proof Γ (mulPredecessorResult (.fvar t) (.fvar base) (.fvar out)) := by
  apply exsElim hp
  let body : Formula 1 := ∃¹ (Ordinal.zero (.bvar 1) ⋏
    (mulPrefix (.fvar u) (.fvar base) (.bvar 1) (.bvar 0) ⋏ edge (.bvar 0) (.fvar u) (.fvar out)))
  let C := body.free :: shifted Γ
  have hd : ND.Proof C (mulRestrictionResultPayload (.fvar (u+1)) (.fvar (base+1)) (.fvar (out+1)) (.fvar 0)) := by
    have hh : ND.Proof C body.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [body] <;> (try simp only [mulRestrictionResultPayload]) <;> mulCompactSyntax)
  have ee := E.shifted.weaken (fun q hq => List.mem_cons_of_mem body.free hq)
  have result := mulRestrictionResultFromPayload ee (t+1) (u+1) (base+1) (out+1) 0
    (up (additionInclusiveSeparationShift hsep) body.free)
    (up (domainShift t ht) body.free) (up (Ordinal.successorShift t u hs) body.free) hd
  convert result using 1 <;> (dsimp [C,body] <;> (try simp only [mulPredecessorResult]) <;> mulCompactSyntax)

#print axioms mulResultPredecessor
end M6.PA.RelationalSource.PairGraph
