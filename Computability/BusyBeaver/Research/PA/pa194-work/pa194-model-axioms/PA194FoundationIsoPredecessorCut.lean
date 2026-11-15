import PA194FoundationIsoPredecessorBijection
set_option maxHeartbeats 5000000
namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND
open Ordinal (Formula)

/-- Separation constructs an actual order-isomorphism between predecessor containers. -/
def predecessorCutIsoDirect {Γ : List Form} (E : FormulaEquality Γ) (g a b p q : Nat)
    (hsep : ND.Proof Γ (separationFormula (strictEntryProperty (.fvar p))))
    (hg : ND.Proof Γ (orderBijection (.fvar g) (.fvar a) (.fvar b)))
    (hp : ND.Proof Γ (Ordinal.successor (.fvar p) (.fvar a)))
    (hq : ND.Proof Γ (Ordinal.successor (.fvar q) (.fvar b)))
    (he : ND.Proof Γ (edge (.fvar g) (.fvar p) (.fvar q))) :
    ND.Proof Γ (orderIso (.fvar p) (.fvar q)) := by
  apply exsElim (strictCutExists p g hsep)
  let body : Formula 1 := strictGraphCut (.fvar p) (.fvar g) (.bvar 0)
  let C := body.free :: shifted Γ
  have cut : ND.Proof C (strictGraphCut (.fvar (p+1)) (.fvar (g+1)) (.fvar 0)) := by
    have h : ND.Proof C body.free := assumption (by simp [C])
    convert h using 1 <;> (dsimp [body] <;> restrictionSyntax)
  let EE := E.shifted.weaken (fun r hr => List.mem_cons_of_mem body.free hr)
  have hg' : ND.Proof C (orderBijection (.fvar (g+1)) (.fvar (a+1)) (.fvar (b+1))) := by
    have h := up (shiftProof hg) body.free
    convert h using 1 <;> isoSyntax
  have hp' : ND.Proof C (Ordinal.successor (.fvar (p+1)) (.fvar (a+1))) := by
    have h := up (shiftProof hp) body.free
    convert h using 1 <;> isoSyntax
  have hq' : ND.Proof C (Ordinal.successor (.fvar (q+1)) (.fvar (b+1))) := by
    have h := up (shiftProof hq) body.free
    convert h using 1 <;> isoSyntax
  have he' : ND.Proof C (edge (.fvar (g+1)) (.fvar (p+1)) (.fvar (q+1))) := by
    have h := up (shiftProof he) body.free
    convert h using 1 <;> isoSyntax
  have entries := strictCutEntries (p+1) (g+1) 0 (a+1) (b+1) cut (andLeft (andRight hg'))
  have restricted := strictCutEdges EE.core EE.transitive (p+1) (g+1) 0 cut
  have bijection := predecessorOrderBijection (g+1) (a+1) (b+1) (p+1) (q+1) 0 hg' hp' hq' he' entries restricted
  have out : ND.Proof C (orderIso (.fvar (p+1)) (.fvar (q+1))) := by
    apply exsIntro _ (.fvar 0)
    convert bijection using 1 <;> isoSyntax
  convert out using 1 <;> (try dsimp [C,body]) <;> (try restrictionSyntax)

#print axioms predecessorCutIsoDirect
end M6.PA.RelationalSource.PairGraph
