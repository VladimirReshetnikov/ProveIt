import PA194FoundationStrictSeparation
import PA194FoundationOrdinalGraphOrder
import PA194FoundationIsoPredecessorCut
import PA194OrderIsoSuccessorImage
import PA194FoundationOrdinalInductionMembers
set_option maxHeartbeats 5000000
namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND
open Ordinal (Formula)

/-- A successor-image witness has an isomorphic predecessor, using the strict cut. -/
def successorMatchFromGraphDirect {Γ : List Form} (E : FormulaEquality Γ) (g a b p : Nat)
    (hsep : ND.Proof Γ (separationFormula (strictEntryProperty (.fvar p))))
    (hg : ND.Proof Γ (orderBijection (.fvar g) (.fvar a) (.fvar b)))
    (hb : ND.Proof Γ (Ordinal.domain (.fvar b)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar p) (.fvar a))) :
    ND.Proof Γ (∃⁰ (Ordinal.domain (.bvar 0) ⋏
      (Ordinal.successor (.bvar 0) (Rew.bShift (.fvar b)) ⋏
       orderIso (Rew.bShift (.fvar p)) (.bvar 0)))) := by
  have hex := successorImageWitness E g p a b hs hg hb
  apply exsElim hex
  let φ : Formula 1 := edge (Rew.bShift (.fvar g)) (Rew.bShift (.fvar p)) (.bvar 0) ⋏
    Ordinal.successor (.bvar 0) (Rew.bShift (.fvar b))
  let C := φ.free :: shifted Γ
  have pair : ND.Proof C (edge (.fvar (g+1)) (.fvar (p+1)) (.fvar 0) ⋏
      Ordinal.successor (.fvar 0) (.fvar (b+1))) := by
    have h : ND.Proof C φ.free := assumption (by simp [C])
    convert h using 1 <;> (dsimp [φ] <;> isoSyntax)
  let EE := E.shifted.weaken (fun r hr => List.mem_cons_of_mem φ.free hr)
  have hg' : ND.Proof C (orderBijection (.fvar (g+1)) (.fvar (a+1)) (.fvar (b+1))) := by
    have h := up (shiftProof hg) φ.free
    convert h using 1 <;> isoSyntax
  have hb' : ND.Proof C (Ordinal.domain (.fvar (b+1))) := by
    have h := up (shiftProof hb) φ.free
    convert h using 1 <;> isoSyntax
  have hs' : ND.Proof C (Ordinal.successor (.fvar (p+1)) (.fvar (a+1))) := by
    have h := up (shiftProof hs) φ.free
    convert h using 1 <;> isoSyntax
  have hsep' : ND.Proof C (separationFormula (strictEntryProperty (.fvar (p+1)))) := by
    have h := up (shiftProof hsep) φ.free
    convert h using 1 <;> restrictionSyntax
  have hm := successorMember EE.core 0 (b+1) (andRight pair)
  have hd := Ordinal.memberDomain (b+1) 0 hb' hm
  have hi := predecessorCutIsoDirect EE (g+1) (a+1) (b+1) (p+1) 0 hsep' hg' hs' (andRight pair) (andLeft pair)
  let ψ : Formula 1 := Ordinal.domain (.bvar 0) ⋏
    (Ordinal.successor (.bvar 0) (.fvar (b+1)) ⋏ orderIso (.fvar (p+1)) (.bvar 0))
  have hw : ND.Proof C (ψ/[.fvar 0]) := by
    convert andIntro hd (andIntro (andRight pair) hi) using 1 <;> (dsimp [ψ] <;> isoSyntax)
  have out := exsIntro ψ (.fvar 0) hw
  convert out using 1 <;> (try dsimp [ψ]) <;> (try isoSyntax)

def isoPredecessorMatch {n : Nat} (p b : Ordinal.Term n) : Ordinal.Formula n :=
  ∃⁰ (Ordinal.domain (.bvar 0) ⋏
    (Ordinal.successor (.bvar 0) (Rew.bShift b) ⋏ orderIso (Rew.bShift p) (.bvar 0)))

/-- Any ordinal isomorphic to a displayed successor has an isomorphic predecessor. -/
def orderIsoSuccessorMatchDirect {Γ : List Form} (E : FormulaEquality Γ) (a b p : Nat)
    (hsep : ND.Proof Γ (separationFormula (strictEntryProperty (.fvar p))))
    (hb : ND.Proof Γ (Ordinal.domain (.fvar b)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar p) (.fvar a)))
    (hi : ND.Proof Γ (orderIso (.fvar a) (.fvar b))) :
    ND.Proof Γ (isoPredecessorMatch (.fvar p) (.fvar b)) := by
  apply exsElim hi
  let body : Formula 1 := orderBijection (.bvar 0) (.fvar a) (.fvar b)
  let C := body.free :: shifted Γ
  have hg : ND.Proof C (orderBijection (.fvar 0) (.fvar (a+1)) (.fvar (b+1))) := by
    have h : ND.Proof C body.free := assumption (by simp [C])
    convert h using 1 <;> (dsimp [body] <;> isoSyntax)
  let EE := E.shifted.weaken (fun r hr => List.mem_cons_of_mem body.free hr)
  have hb' : ND.Proof C (Ordinal.domain (.fvar (b+1))) := by
    have h := up (shiftProof hb) body.free
    convert h using 1 <;> isoSyntax
  have hs' : ND.Proof C (Ordinal.successor (.fvar (p+1)) (.fvar (a+1))) := by
    have h := up (shiftProof hs) body.free
    convert h using 1 <;> isoSyntax
  have hsep' : ND.Proof C (separationFormula (strictEntryProperty (.fvar (p+1)))) := by
    have h := up (shiftProof hsep) body.free
    convert h using 1 <;> restrictionSyntax
  have out := successorMatchFromGraphDirect EE 0 (a+1) (b+1) (p+1) hsep' hg hb' hs'
  convert out using 1 <;> (try dsimp [C,body,isoPredecessorMatch]) <;> (try isoSyntax)

def orderIsoSuccessorMatchClosed {Γ : List Form} (E : FormulaEquality Γ) (a b p : Nat)
    (hsep : ND.Proof Γ closedStrictSeparation)
    (hb : ND.Proof Γ (Ordinal.domain (.fvar b)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar p) (.fvar a)))
    (hi : ND.Proof Γ (orderIso (.fvar a) (.fvar b))) :
    ND.Proof Γ (isoPredecessorMatch (.fvar p) (.fvar b)) :=
  orderIsoSuccessorMatchDirect E a b p (strictSeparationAt p hsep) hb hs hi

#print axioms orderIsoSuccessorMatchClosed
#print axioms orderIsoSuccessorMatchDirect
#print axioms successorMatchFromGraphDirect
end M6.PA.RelationalSource.PairGraph
