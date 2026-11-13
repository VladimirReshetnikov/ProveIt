module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIdentityBijectionTotal
@[expose] public section

/-! Functionality and injectivity of actual diagonal identity edges. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def identityFunctional {Γ : List Form} (E : FormulaEquality Γ) (g a : Nat)
    (hg : ND.Proof Γ (identityDiagonal (.fvar g) (.fvar a))) :
    ND.Proof Γ (graphFunctional (.fvar g)) := by
  apply allIntro
  apply allIntro
  apply allIntro
  let d : Form := edge (.fvar (g+1+1+1)) (.fvar 2) (.fvar 1) ⋏
    edge (.fvar (g+1+1+1)) (.fvar 2) (.fvar 0)
  have hd : ND.Proof (d :: shifted (shifted (shifted Γ))) d := assumption (by simp)
  have ee := E.shifted.shifted.shifted.weaken (fun p hp => List.mem_cons_of_mem d hp)
  have hh := up (identityDiagonalShift (g+1+1) (a+1+1)
    (identityDiagonalShift (g+1) (a+1) (identityDiagonalShift g a hg))) d
  have out := identityFunctionalAt ee (g+1+1+1) (a+1+1+1) 2 1 0 hh (andLeft hd) (andRight hd)
  convert impIntro out using 1 <;> (dsimp [d] <;> isoSyntax)

def identityInjective {Γ : List Form} (E : FormulaEquality Γ) (g a : Nat)
    (hg : ND.Proof Γ (identityDiagonal (.fvar g) (.fvar a))) :
    ND.Proof Γ (graphInjective (.fvar g)) := by
  apply allIntro
  apply allIntro
  apply allIntro
  let d : Form := edge (.fvar (g+1+1+1)) (.fvar 2) (.fvar 0) ⋏
    edge (.fvar (g+1+1+1)) (.fvar 1) (.fvar 0)
  have hd : ND.Proof (d :: shifted (shifted (shifted Γ))) d := assumption (by simp)
  have ee := E.shifted.shifted.shifted.weaken (fun p hp => List.mem_cons_of_mem d hp)
  have hh := up (identityDiagonalShift (g+1+1) (a+1+1)
    (identityDiagonalShift (g+1) (a+1) (identityDiagonalShift g a hg))) d
  have out := identityInjectiveAt ee (g+1+1+1) (a+1+1+1) 2 1 0 hh (andLeft hd) (andRight hd)
  convert impIntro out using 1 <;> (dsimp [d] <;> isoSyntax)

#print axioms identityFunctional
#print axioms identityInjective
end M6.PA.RelationalSource.PairGraph
