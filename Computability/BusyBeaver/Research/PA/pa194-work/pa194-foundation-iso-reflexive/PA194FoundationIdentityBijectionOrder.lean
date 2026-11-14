import PA194FoundationIdentityBijectionUnique

/-! Membership-order equivalence for the identity graph; ordinary equality
supplies both directions without any equality of graph objects. -/
namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND

def identityOrder {Γ : List Form} (E : FormulaEquality Γ) (g a : Nat)
    (hg : ND.Proof Γ (identityDiagonal (.fvar g) (.fvar a))) :
    ND.Proof Γ (graphOrder (.fvar g)) := by
  apply allIntro
  apply allIntro
  apply allIntro
  apply allIntro
  let d : Form := edge (.fvar (g+1+1+1+1)) (.fvar 3) (.fvar 1) ⋏
    edge (.fvar (g+1+1+1+1)) (.fvar 2) (.fvar 0)
  have hd : ND.Proof (d :: shifted (shifted (shifted (shifted Γ)))) d := assumption (by simp)
  have ee := E.shifted.shifted.shifted.shifted.weaken (fun p hp => List.mem_cons_of_mem d hp)
  have hh := up (identityDiagonalShift (g+1+1+1) (a+1+1+1)
    (identityDiagonalShift (g+1+1) (a+1+1)
      (identityDiagonalShift (g+1) (a+1) (identityDiagonalShift g a hg)))) d
  have out := identityOrderAt ee (g+1+1+1+1) (a+1+1+1+1) 3 2 1 0 hh (andLeft hd) (andRight hd)
  convert impIntro out using 1 <;> (dsimp [d] <;> isoSyntax)

def identityBijection {Γ : List Form} (E : FormulaEquality Γ) (g a : Nat)
    (hg : ND.Proof Γ (identityGraph (.fvar g) (.fvar a))) :
    ND.Proof Γ (orderBijection (.fvar g) (.fvar a) (.fvar a)) :=
  andIntro (andLeft hg)
    (andIntro (identityTyped E g a (andLeft (andRight hg)))
      (andIntro (identityLeftTotal g a (andRight (andRight hg)))
        (andIntro (identityRightTotal g a (andRight (andRight hg)))
          (andIntro (identityFunctional E g a (andLeft (andRight hg)))
            (andIntro (identityInjective E g a (andLeft (andRight hg)))
              (identityOrder E g a (andLeft (andRight hg))))))))

def orderIsoFromIdentity {Γ : List Form} (E : FormulaEquality Γ) (g a : Nat)
    (hg : ND.Proof Γ (identityGraph (.fvar g) (.fvar a))) :
    ND.Proof Γ (orderIso (.fvar a) (.fvar a)) := by
  apply exsIntro _ (.fvar g)
  convert identityBijection E g a hg using 1 <;> isoSyntax

#print axioms identityOrder
#print axioms identityBijection
#print axioms orderIsoFromIdentity
end M6.PA.RelationalSource.PairGraph
