import PA194FoundationIsoPredecessorCut
import PA194FoundationIsoEndpointEdge
set_option maxHeartbeats 5000000
namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND
open Ordinal (Formula)

/-- Successor cancellation, from an explicit parameterized strict-cut Separation instance. -/
def orderIsoSuccessorCancelDirect {Γ : List Form} (E : FormulaEquality Γ) (a b p q : Nat)
    (hsep : ND.Proof Γ (separationFormula (strictEntryProperty (.fvar p))))
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
  have hs : ND.Proof C (Ordinal.successor (.fvar (p+1)) (.fvar (a+1))) := by
    have h := up (shiftProof hp) body.free
    convert h using 1 <;> isoSyntax
  have ht : ND.Proof C (Ordinal.successor (.fvar (q+1)) (.fvar (b+1))) := by
    have h := up (shiftProof hq) body.free
    convert h using 1 <;> isoSyntax
  have hd : ND.Proof C (Ordinal.domain (.fvar (b+1))) := by
    have h := up (shiftProof hb) body.free
    convert h using 1 <;> isoSyntax
  have hsep' : ND.Proof C (separationFormula (strictEntryProperty (.fvar (p+1)))) := by
    have h := up (shiftProof hsep) body.free
    convert h using 1 <;> restrictionSyntax
  have he := successorEndpointsEdge EE 0 (a+1) (b+1) (p+1) (q+1) hg hd hs ht
  have out := predecessorCutIsoDirect EE 0 (a+1) (b+1) (p+1) (q+1) hsep' hg hs ht he
  convert out using 1 <;> (try dsimp [C,body]) <;> (try isoSyntax)

#print axioms orderIsoSuccessorCancelDirect
end M6.PA.RelationalSource.PairGraph
