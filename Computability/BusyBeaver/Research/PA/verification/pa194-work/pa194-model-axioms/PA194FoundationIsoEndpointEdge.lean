import PA194OrderIsoSuccessorImage
import PA194FoundationOrdinalGraphOrder
set_option maxHeartbeats 5000000
namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND
open Ordinal (Formula)

def endpointEdgeOutputTransport {Γ : List Form} (E : FormulaEquality Γ) (g p q r : Nat)
    (heq : ND.Proof Γ (eq (.fvar q) (.fvar r)))
    (he : ND.Proof Γ (edge (.fvar g) (.fvar p) (.fvar q))) :
    ND.Proof Γ (edge (.fvar g) (.fvar p) (.fvar r)) := by
  have hp : ND.Proof Γ (Semiformula.rewAux (Rew.subst ![.fvar q])
      (edge (.fvar g) (.fvar p) (.bvar 0))) := by
    convert he using 1 <;> isoSyntax
  have out := E.substituteOne (edge (.fvar g) (.fvar p) (.bvar 0)) (.fvar q) (.fvar r) heq hp
  convert out using 1 <;> isoSyntax

/-- A bijection between displayed successors sends the left predecessor to the right predecessor. -/
def successorEndpointsEdge {Γ : List Form} (E : FormulaEquality Γ) (g a b p q : Nat)
    (hg : ND.Proof Γ (orderBijection (.fvar g) (.fvar a) (.fvar b)))
    (hb : ND.Proof Γ (Ordinal.domain (.fvar b)))
    (hp : ND.Proof Γ (Ordinal.successor (.fvar p) (.fvar a)))
    (hq : ND.Proof Γ (Ordinal.successor (.fvar q) (.fvar b))) :
    ND.Proof Γ (edge (.fvar g) (.fvar p) (.fvar q)) := by
  have hex := successorImageWitness E g p a b hp hg hb
  apply exsElim hex
  let φ : Formula 1 := edge (Rew.bShift (.fvar g)) (Rew.bShift (.fvar p)) (.bvar 0) ⋏
    Ordinal.successor (.bvar 0) (Rew.bShift (.fvar b))
  let C := φ.free :: shifted Γ
  have pair : ND.Proof C (edge (.fvar (g+1)) (.fvar (p+1)) (.fvar 0) ⋏
      Ordinal.successor (.fvar 0) (.fvar (b+1))) := by
    have h : ND.Proof C φ.free := assumption (by simp [C])
    convert h using 1 <;> (dsimp [φ] <;> isoSyntax)
  let EE := E.shifted.weaken (fun r hr => List.mem_cons_of_mem φ.free hr)
  have hb' : ND.Proof C (Ordinal.domain (.fvar (b+1))) := by
    have h := up (shiftProof hb) φ.free
    convert h using 1 <;> isoSyntax
  have hq' : ND.Proof C (Ordinal.successor (.fvar (q+1)) (.fvar (b+1))) := by
    have h := up (shiftProof hq) φ.free
    convert h using 1 <;> isoSyntax
  have eqp := successorPredecessorUnique EE.core (b+1) 0 (q+1) hb' (andRight pair) hq'
  have out := endpointEdgeOutputTransport EE (g+1) (p+1) 0 (q+1) eqp (andLeft pair)
  convert out using 1 <;> (try dsimp [C,φ]) <;> (try isoSyntax)

#print axioms endpointEdgeOutputTransport
#print axioms successorEndpointsEdge
end M6.PA.RelationalSource.PairGraph
