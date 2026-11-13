module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoPredecessorImage
public import M6PA.Calibration.RelationalIsoSuccessorFrame
@[expose] public section

/-! A bijection between two successor containers relates their displayed
predecessors. This uses actual left-totality and local predecessor uniqueness. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
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

def successorEndpointsEdge {Γ : List Form} (E : FormulaEquality Γ) (g a b p r : Nat)
    (hg : ND.Proof Γ (orderBijection (.fvar g) (.fvar a) (.fvar b)))
    (hb : ND.Proof Γ (Ordinal.domain (.fvar b)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar p) (.fvar a)))
    (hr : ND.Proof Γ (Ordinal.successor (.fvar r) (.fvar b))) :
    ND.Proof Γ (edge (.fvar g) (.fvar p) (.fvar r)) := by
  have hm := successorMember E.core p a hs
  have hl := andLeft (andRight (andRight hg))
  apply exsElim (orderLeftAt g a p hl hm)
  let body : Formula 1 := edge (.fvar g) (.fvar p) (.bvar 0)
  let C := body.free :: shifted Γ
  have he : ND.Proof C (edge (.fvar (g+1)) (.fvar (p+1)) (.fvar 0)) := by
    have h : ND.Proof C body.free := assumption (by simp [C])
    convert h using 1 <;> (dsimp [body] <;> isoSyntax)
  let EE := E.shifted.weaken (fun q hq => List.mem_cons_of_mem body.free hq)
  have equality := successorImageUnique EE (g+1) (a+1) (b+1) (p+1) 0 (r+1)
    (up (orderBijectionShift g a b hg) body.free) (up (Ordinal.domainShift b hb) body.free)
    (up (Ordinal.successorShift p a hs) body.free) (up (Ordinal.successorShift r b hr) body.free) he
  have out := endpointEdgeOutputTransport EE (g+1) (p+1) 0 (r+1) equality he
  convert out using 1 <;> (dsimp [C,body] <;> isoSyntax)

#print axioms endpointEdgeOutputTransport
#print axioms successorEndpointsEdge
end M6.PA.RelationalSource.PairGraph
