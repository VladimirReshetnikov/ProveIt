module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoGreatestImage
@[expose] public section

/-! The image of a successor endpoint is an actual ordinal predecessor,
with all five domain clauses inherited from the target representative. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def successorImagePredecessor {Γ : List Form} (E : FormulaEquality Γ) (g a b p q : Nat)
    (hg : ND.Proof Γ (orderBijection (.fvar g) (.fvar a) (.fvar b)))
    (hb : ND.Proof Γ (Ordinal.domain (.fvar b)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar p) (.fvar a)))
    (he : ND.Proof Γ (edge (.fvar g) (.fvar p) (.fvar q))) :
    ND.Proof Γ (Ordinal.domain (.fvar q) ⋏ Ordinal.successor (.fvar q) (.fvar b)) := by
  have typed := andLeft (andRight hg)
  have rightTotal := andLeft (andRight (andRight (andRight hg)))
  have functional := andLeft (andRight (andRight (andRight (andRight hg))))
  have ordered := andRight (andRight (andRight (andRight (andRight (andRight hg)))))
  have member := andRight (orderTypedAt g a b p q typed he)
  have greatest := imageGreatest E g a b p q typed rightTotal functional ordered
    (successorGreatest E.core p a hs) he
  exact andIntro (Ordinal.memberDomain b q hb member)
    (Ordinal.greatestSuccessor E.core b q (andLeft (andLeft hb)) greatest)

def successorImageUnique {Γ : List Form} (E : FormulaEquality Γ) (g a b p q r : Nat)
    (hg : ND.Proof Γ (orderBijection (.fvar g) (.fvar a) (.fvar b)))
    (hb : ND.Proof Γ (Ordinal.domain (.fvar b)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar p) (.fvar a)))
    (hr : ND.Proof Γ (Ordinal.successor (.fvar r) (.fvar b)))
    (he : ND.Proof Γ (edge (.fvar g) (.fvar p) (.fvar q))) :
    ND.Proof Γ (eq (.fvar q) (.fvar r)) :=
  successorPredecessorUnique E.core b q r hb
    (andRight (successorImagePredecessor E g a b p q hg hb hs he)) hr

#print axioms successorImagePredecessor
#print axioms successorImageUnique
end M6.PA.RelationalSource.PairGraph
