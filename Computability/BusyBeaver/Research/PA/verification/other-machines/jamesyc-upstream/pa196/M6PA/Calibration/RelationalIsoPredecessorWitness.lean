module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoPredecessorImage
public import M6PA.Calibration.RelationalIsoSuccessorFrame
@[expose] public section

/-! A real graph edge supplies an actual ordinal predecessor witness. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Formula)

def imagePredecessorExists (g p b : Ordinal.Term n) : Formula n :=
  ∃¹ (Ordinal.domain (.bvar 0) ⋏
    (Ordinal.successor (.bvar 0) (Rew.bShift b) ⋏
      edge (Rew.bShift g) (Rew.bShift p) (.bvar 0)))

def successorImageWitness {Γ : List Form} (E : FormulaEquality Γ) (g a b p : Nat)
    (hg : ND.Proof Γ (orderBijection (.fvar g) (.fvar a) (.fvar b)))
    (hb : ND.Proof Γ (Ordinal.domain (.fvar b)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar p) (.fvar a))) :
    ND.Proof Γ (imagePredecessorExists (.fvar g) (.fvar p) (.fvar b)) := by
  have hm := successorMember E.core p a hs
  have hl := andLeft (andRight (andRight hg))
  apply exsElim (orderLeftAt g a p hl hm)
  let body : Formula 1 := edge (.fvar g) (.fvar p) (.bvar 0)
  let C := body.free :: shifted Γ
  have he : ND.Proof C (edge (.fvar (g+1)) (.fvar (p+1)) (.fvar 0)) := by
    have h : ND.Proof C body.free := assumption (by simp [C])
    convert h using 1 <;> (dsimp [body] <;> isoSyntax)
  have out := successorImagePredecessor
    (E.shifted.weaken (fun r hr => List.mem_cons_of_mem body.free hr))
    (g+1) (a+1) (b+1) (p+1) 0 (up (orderBijectionShift g a b hg) body.free)
    (up (Ordinal.domainShift b hb) body.free) (up (Ordinal.successorShift p a hs) body.free) he
  have result : ND.Proof C (imagePredecessorExists (.fvar (g+1)) (.fvar (p+1)) (.fvar (b+1))) := by
    apply exsIntro _ (.fvar 0)
    convert andIntro (andLeft out) (andIntro (andRight out) he) using 1 <;>
      ((try simp only [imagePredecessorExists]) <;> isoSyntax)
  convert result using 1 <;> (dsimp [C,body] <;> (try simp only [imagePredecessorExists]) <;> isoSyntax)

#print axioms successorImageWitness
end M6.PA.RelationalSource.PairGraph
