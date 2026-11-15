import PA194OrderIsoGreatestExists
import PA194GreatestSuccessorClosedTemplate
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND
open Ordinal

def successorHasGreatest {Γ : List Form} (E : FormulaEquality Γ) (a s : Nat)
    (hs : ND.Proof Γ (Ordinal.successor (.fvar a) (.fvar s))) :
    ND.Proof Γ (Ordinal.greatest (.fvar s) (.fvar a)) := by
  have heq := E.reflexive (.fvar a)
  have ha : ND.Proof Γ (mem (.fvar s) (.fvar a)) :=
    mp (orRight heq) (andRight (successorAt a s a hs))
  apply andIntro ha
  apply allIntro
  let z : Form := mem (.fvar (s+1)) (.fvar 0)
  let D := z :: shifted Γ
  have hz : ND.Proof D z := assumption (by simp [D])
  have hs' : ND.Proof D (Ordinal.successor (.fvar (a+1)) (.fvar (s+1))) := by
    have h := up (shiftProof hs) z
    convert h using 1 <;> isoSyntax
  have cases := mp hz (andLeft (successorAt (a+1) (s+1) 0 hs'))
  have result : ND.Proof D (eq (.fvar 0) (.fvar (a+1)) ⋎ mem (.fvar (a+1)) (.fvar 0)) := by
    apply orElim cases
    · exact orRight (assumption (by simp))
    · exact orLeft (assumption (by simp))
  have out := impIntro result
  convert out using 1 <;> (try dsimp [D,z]) <;> (try isoSyntax)

/-- A bijection from a successor to an ordinal sends its top point to a predecessor of the target. -/
def successorImageWitness {Γ : List Form} (E : FormulaEquality Γ) (g a s b : Nat)
    (hs : ND.Proof Γ (Ordinal.successor (.fvar a) (.fvar s)))
    (hb : ND.Proof Γ (orderBijection (.fvar g) (.fvar s) (.fvar b)))
    (hd : ND.Proof Γ (Ordinal.domain (.fvar b))) :
    ND.Proof Γ (∃⁰ (edge (Rew.bShift (.fvar g)) (Rew.bShift (.fvar a)) (.bvar 0) ⋏
      Ordinal.successor (.bvar 0) (Rew.bShift (.fvar b)))) := by
  have hg := successorHasGreatest E a s hs
  have hex := greatestImageExists E g s b a hb hg
  apply exsElim hex
  let φ : Formula 1 := edge (Rew.bShift (.fvar g)) (Rew.bShift (.fvar a)) (.bvar 0) ⋏
    Ordinal.greatest (Rew.bShift (.fvar b)) (.bvar 0)
  let D := φ.free :: shifted Γ
  have hpair : ND.Proof D (edge (.fvar (g+1)) (.fvar (a+1)) (.fvar 0) ⋏
      Ordinal.greatest (.fvar (b+1)) (.fvar 0)) := by
    have h : ND.Proof D φ.free := assumption (by simp [D])
    convert h using 1 <;> (dsimp [φ] <;> isoSyntax)
  let E' := E.shifted.weaken (fun p hp => List.mem_cons_of_mem φ.free hp)
  have hd' : ND.Proof D (Ordinal.domain (.fvar (b+1))) := by
    have h := up (shiftProof hd) φ.free
    convert h using 1 <;> isoSyntax
  have hsucc := greatestSuccessor E'.core (b+1) 0 (andLeft (andLeft hd')) (andRight hpair)
  let ψ : Formula 1 := edge (.fvar (g+1)) (.fvar (a+1)) (.bvar 0) ⋏
    Ordinal.successor (.bvar 0) (.fvar (b+1))
  have hw : ND.Proof D (ψ/[.fvar 0]) := by
    convert andIntro (andLeft hpair) hsucc using 1 <;> (dsimp [ψ] <;> isoSyntax)
  have out := exsIntro ψ (.fvar 0) hw
  convert out using 1 <;> (try dsimp [ψ]) <;> (try isoSyntax)

#print axioms successorHasGreatest
#print axioms successorImageWitness
end M6.PA.RelationalSource.PairGraph
