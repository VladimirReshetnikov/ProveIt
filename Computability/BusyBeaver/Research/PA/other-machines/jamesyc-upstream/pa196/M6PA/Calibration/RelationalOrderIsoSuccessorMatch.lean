module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoSuccessorMatchGraph
@[expose] public section

/-! Any representative isomorphic to a displayed successor has a genuine
ordinal predecessor isomorphic to the original predecessor. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Formula)
attribute [local irreducible] orderIso
set_option maxHeartbeats 600000

def orderIsoSuccessorMatch {Γ : List Form} (E : FormulaEquality Γ) (a b p : Nat)
    (hsep : ND.Proof Γ closedStrictSeparation)
    (hb : ND.Proof Γ (Ordinal.domain (.fvar b)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar p) (.fvar a)))
    (hi : ND.Proof Γ (orderIso (.fvar a) (.fvar b))) :
    ND.Proof Γ (isoPredecessorMatch (.fvar p) (.fvar b)) := by
  have hex : ND.Proof Γ (∃¹ orderBijection (.bvar 0) (.fvar a) (.fvar b)) := by
    simpa only [orderIso,Rew.bShift_fvar] using hi
  apply exsElim hex
  let body : Formula 1 := orderBijection (.bvar 0) (.fvar a) (.fvar b)
  let C := body.free :: shifted Γ
  have hg : ND.Proof C (orderBijection (.fvar 0) (.fvar (a+1)) (.fvar (b+1))) := by
    have hh : ND.Proof C body.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [body] <;> isoSyntax)
  have out := successorMatchFromGraph
    (E.shifted.weaken (fun r hr => List.mem_cons_of_mem body.free hr)) 0 (a+1) (b+1) (p+1)
    (up (predecessorClosedSeparationShift hsep) body.free) hg
    (up (Ordinal.domainShift b hb) body.free) (up (Ordinal.successorShift p a hs) body.free)
  convert out using 1 <;> (dsimp [C,body] <;> (try simp only [isoPredecessorMatch]) <;> isoSyntax)

#print axioms orderIsoSuccessorMatch
end M6.PA.RelationalSource.PairGraph
