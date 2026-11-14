import PA194FoundationIdentityTotalExtension

/-! Ordinary equality turns diagonal identity edges into the pointwise
bijection and order laws. No extensionality of graph objects is used. -/
namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND

def identityTypedAt {Γ : List Form} (E : FormulaEquality Γ) (g a x y : Nat)
    (hg : ND.Proof Γ (identityDiagonal (.fvar g) (.fvar a)))
    (he : ND.Proof Γ (edge (.fvar g) (.fvar x) (.fvar y))) :
    ND.Proof Γ (mem (.fvar a) (.fvar x) ⋏ mem (.fvar a) (.fvar y)) := by
  have h := identityDiagonalAt g a x y hg he
  exact andIntro (andLeft h) (Ordinal.memElement E.core a x y (andRight h) (andLeft h))

def identityFunctionalAt {Γ : List Form} (E : FormulaEquality Γ) (g a x y z : Nat)
    (hg : ND.Proof Γ (identityDiagonal (.fvar g) (.fvar a)))
    (hy : ND.Proof Γ (edge (.fvar g) (.fvar x) (.fvar y)))
    (hz : ND.Proof Γ (edge (.fvar g) (.fvar x) (.fvar z))) :
    ND.Proof Γ (eq (.fvar y) (.fvar z)) :=
  Ordinal.eqTrans E.transitive y x z
    (Ordinal.eqSymm E.core x y (andRight (identityDiagonalAt g a x y hg hy)))
    (andRight (identityDiagonalAt g a x z hg hz))

def identityInjectiveAt {Γ : List Form} (E : FormulaEquality Γ) (g a x y z : Nat)
    (hg : ND.Proof Γ (identityDiagonal (.fvar g) (.fvar a)))
    (hx : ND.Proof Γ (edge (.fvar g) (.fvar x) (.fvar z)))
    (hy : ND.Proof Γ (edge (.fvar g) (.fvar y) (.fvar z))) :
    ND.Proof Γ (eq (.fvar x) (.fvar y)) :=
  Ordinal.eqTrans E.transitive x z y
    (andRight (identityDiagonalAt g a x z hg hx))
    (Ordinal.eqSymm E.core y z (andRight (identityDiagonalAt g a y z hg hy)))

def identityOrderAt {Γ : List Form} (E : FormulaEquality Γ) (g a x u y v : Nat)
    (hg : ND.Proof Γ (identityDiagonal (.fvar g) (.fvar a)))
    (hxy : ND.Proof Γ (edge (.fvar g) (.fvar x) (.fvar y)))
    (huv : ND.Proof Γ (edge (.fvar g) (.fvar u) (.fvar v))) :
    ND.Proof Γ (sourceIff (mem (.fvar x) (.fvar u)) (mem (.fvar y) (.fvar v))) := by
  have exy := andRight (identityDiagonalAt g a x y hg hxy)
  have euv := andRight (identityDiagonalAt g a u v hg huv)
  apply andIntro
  · apply impIntro
    let d : Form := mem (.fvar x) (.fvar u)
    exact Ordinal.memCongr (E.core.up d) x y u v (up exy d) (up euv d) (assumption (by simp [d]))
  · apply impIntro
    let d : Form := mem (.fvar y) (.fvar v)
    exact Ordinal.memCongr (E.core.up d) y x v u
      (up (Ordinal.eqSymm E.core x y exy) d) (up (Ordinal.eqSymm E.core u v euv) d)
      (assumption (by simp [d]))

#print axioms identityTypedAt
#print axioms identityFunctionalAt
#print axioms identityInjectiveAt
#print axioms identityOrderAt
end M6.PA.RelationalSource.PairGraph
