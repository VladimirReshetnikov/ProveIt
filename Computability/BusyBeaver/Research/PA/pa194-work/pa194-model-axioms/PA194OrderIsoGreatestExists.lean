import PA194OrderIsoExtrema
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND
open Ordinal (Term Formula)

def leftTotalAtLocal {Γ : List Form} (g a x : Nat)
    (ht : ND.Proof Γ (graphLeftTotal (.fvar g) (.fvar a)))
    (hx : ND.Proof Γ (mem (.fvar a) (.fvar x))) :
    ND.Proof Γ (∃⁰ edge (.fvar g) (.fvar x) (.bvar 0)) := by
  have h : ND.Proof Γ (mem (.fvar a) (.fvar x) 🡒 ∃⁰ edge (.fvar g) (.fvar x) (.bvar 0)) := by
    convert allElim _ (.fvar x) ht using 1 <;> isoSyntax
  exact mp hx h

/-- An order-bijection has an edge carrying the greatest source point to the greatest target point. -/
def greatestImageExists {Γ : List Form} (E : FormulaEquality Γ) (g a b x : Nat)
    (hb : ND.Proof Γ (orderBijection (.fvar g) (.fvar a) (.fvar b)))
    (hg : ND.Proof Γ (Ordinal.greatest (.fvar a) (.fvar x))) :
    ND.Proof Γ (∃⁰ (edge (Rew.bShift (.fvar g)) (Rew.bShift (.fvar x)) (.bvar 0) ⋏
      Ordinal.greatest (Rew.bShift (.fvar b)) (.bvar 0))) := by
  have hl := andLeft (andRight (andRight hb))
  have hex := leftTotalAtLocal g a x hl (andLeft hg)
  apply exsElim hex
  let φ : Formula 1 := edge (.fvar g) (.fvar x) (.bvar 0)
  let D := φ.free :: shifted Γ
  have he : ND.Proof D (edge (.fvar (g+1)) (.fvar (x+1)) (.fvar 0)) := by
    have h : ND.Proof D φ.free := assumption (by simp [D])
    convert h using 1 <;> (dsimp [φ] <;> isoSyntax)
  let E' := E.shifted.weaken (fun p hp => List.mem_cons_of_mem φ.free hp)
  have hb' : ND.Proof D (orderBijection (.fvar (g+1)) (.fvar (a+1)) (.fvar (b+1))) := by
    have h := up (shiftProof hb) φ.free
    convert h using 1 <;> isoSyntax
  have hg' : ND.Proof D (Ordinal.greatest (.fvar (a+1)) (.fvar (x+1))) := by
    have h := up (shiftProof hg) φ.free
    convert h using 1 <;> isoSyntax
  have hy := greatestImage E' (g+1) (a+1) (b+1) (x+1) 0 hb' hg' he
  let ψ : Formula 1 := edge (.fvar (g+1)) (.fvar (x+1)) (.bvar 0) ⋏
    Ordinal.greatest (.fvar (b+1)) (.bvar 0)
  have hw : ND.Proof D (ψ/[.fvar 0]) := by
    convert andIntro he hy using 1 <;> (dsimp [ψ] <;> isoSyntax)
  have out := exsIntro ψ (.fvar 0) hw
  convert out using 1 <;> (try dsimp [ψ]) <;> (try isoSyntax)

#print axioms leftTotalAtLocal
#print axioms greatestImageExists
end M6.PA.RelationalSource.PairGraph
