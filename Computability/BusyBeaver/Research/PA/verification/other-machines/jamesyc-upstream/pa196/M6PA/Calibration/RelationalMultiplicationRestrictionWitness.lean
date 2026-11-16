module
public import M6PA.Theory
public import M6PA.Calibration.RelationalMultiplicationRestrictionEndpoint
public import M6PA.Calibration.RelationalAdditionRestrictionWitness
@[expose] public section

/-! A predecessor multiplication result from an actual Separation-built subgraph. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)
attribute [local irreducible] addPrefix addResult mulPrefix
set_option maxHeartbeats 600000

set_option maxHeartbeats 600000 in
def mulRestrictionResultFromGraph {Γ : List Form} (E : FormulaEquality Γ)
    (t u base e g out : Nat)
    (hsep : ND.Proof Γ closedInclusiveSeparation)
    (ht : ND.Proof Γ (Ordinal.domain (.fvar t)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar t) (.fvar u)))
    (hz : ND.Proof Γ (Ordinal.zero (.fvar e)))
    (hp : ND.Proof Γ (mulPrefix (.fvar u) (.fvar base) (.fvar e) (.fvar g)))
    (he : ND.Proof Γ (edge (.fvar g) (.fvar u) (.fvar out))) :
    ND.Proof Γ (mulPredecessorResult (.fvar t) (.fvar base) (.fvar out)) := by
  apply exsElim (graphRestrictionWitness E.core E.transitive t g (inclusiveSeparationAt t hsep))
  let body : Formula 1 := graphRestriction (.fvar t) (.fvar g) (.bvar 0)
  let C := body.free :: shifted Γ
  have hr : ND.Proof C (graphRestriction (.fvar (t+1)) (.fvar (g+1)) (.fvar 0)) := by
    have hh : ND.Proof C body.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [body] <;> inclusiveRestrictionSyntax)
  have ee := E.shifted.weaken (fun q hq => List.mem_cons_of_mem body.free hq)
  have pp := up (mulPrefixShift u base e g hp) body.free
  have zz := up (Ordinal.zeroShift e hz) body.free
  have ss := up (Ordinal.successorShift t u hs) body.free
  have restricted := mulRestrictionPrefix ee (t+1) (u+1) (base+1) (e+1) (g+1) 0
    (up (domainShift t ht) body.free) ss zz pp hr
  have parts := pp
  unfold mulPrefix at parts
  have prev := mulRecurrenceAt (g+1) (base+1) (u+1) (out+1) (t+1)
    (andRight (andRight (andRight (andRight parts)))) (up (edgeShift g u out he) body.free) ss
  have result := mulRestrictionEndpointPrevious ee (t+1) (base+1) (e+1) (g+1) 0 (out+1)
    zz restricted hr prev
  convert result using 1 <;> (dsimp [C,body] <;> (try simp only [mulPredecessorResult]) <;> mulCompactSyntax)

#print axioms mulRestrictionResultFromGraph
end M6.PA.RelationalSource.PairGraph
