module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoEndpointEdge
public import M6PA.Calibration.RelationalIsoPredecessorCutWitness
@[expose] public section

/-! Successor cancellation modulo the actual order-isomorphism relation.
The target successor is an ordinal representative and the required closed
Separation instance remains an explicit finite proof input. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Formula)

def orderIsoSuccessorCancel {Γ : List Form} (E : FormulaEquality Γ) (a b p q : Nat)
    (hsep : ND.Proof Γ closedStrictSeparation)
    (hb : ND.Proof Γ (Ordinal.domain (.fvar b)))
    (hp : ND.Proof Γ (Ordinal.successor (.fvar p) (.fvar a)))
    (hq : ND.Proof Γ (Ordinal.successor (.fvar q) (.fvar b)))
    (hi : ND.Proof Γ (orderIso (.fvar a) (.fvar b))) :
    ND.Proof Γ (orderIso (.fvar p) (.fvar q)) := by
  apply exsElim hi
  let body : Formula 1 := orderBijection (.bvar 0) (.fvar a) (.fvar b)
  let C := body.free :: shifted Γ
  have hg : ND.Proof C (orderBijection (.fvar 0) (.fvar (a+1)) (.fvar (b+1))) := by
    have h : ND.Proof C body.free := assumption (by simp [C])
    convert h using 1 <;> (dsimp [body] <;> isoSyntax)
  let EE := E.shifted.weaken (fun r hr => List.mem_cons_of_mem body.free hr)
  have hs := up (Ordinal.successorShift p a hp) body.free
  have ht := up (Ordinal.successorShift q b hq) body.free
  have edge := successorEndpointsEdge EE 0 (a+1) (b+1) (p+1) (q+1) hg
    (up (Ordinal.domainShift b hb) body.free) hs ht
  have out := predecessorCutIso 0 (a+1) (b+1) (p+1) (q+1)
    ⟨EE,up (predecessorClosedSeparationShift hsep) body.free,hg,hs,ht,edge⟩
  convert out using 1 <;> (dsimp [C,body] <;> isoSyntax)

#print axioms orderIsoSuccessorCancel
end M6.PA.RelationalSource.PairGraph
