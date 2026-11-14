import PA194FoundationIdentityBijectionRules

/-! Diagonal identity graphs satisfy typing and both directions of totality. -/
namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND

def identityTyped {Γ : List Form} (E : FormulaEquality Γ) (g a : Nat)
    (hg : ND.Proof Γ (identityDiagonal (.fvar g) (.fvar a))) :
    ND.Proof Γ (graphTyped (.fvar g) (.fvar a) (.fvar a)) := by
  apply allIntro
  apply allIntro
  let d : Form := edge (.fvar (g+1+1)) (.fvar 1) (.fvar 0)
  have hd : ND.Proof (d :: shifted (shifted Γ)) d := assumption (by simp)
  have out := identityTypedAt (E.shifted.shifted.weaken (fun p hp => List.mem_cons_of_mem d hp))
    (g+1+1) (a+1+1) 1 0 (up (identityDiagonalShift (g+1) (a+1) (identityDiagonalShift g a hg)) d) hd
  convert impIntro out using 1 <;> (dsimp [d] <;> isoSyntax)

def identityLeftTotal {Γ : List Form} (g a : Nat)
    (hg : ND.Proof Γ (identityTotal (.fvar g) (.fvar a))) :
    ND.Proof Γ (graphLeftTotal (.fvar g) (.fvar a)) := by
  apply allIntro
  let d : Form := mem (.fvar (a+1)) (.fvar 0)
  have hd : ND.Proof (d :: shifted Γ) d := assumption (by simp)
  have he := identityTotalAt (g+1) (a+1) 0 (up (identityTotalShift g a hg) d) hd
  have out : ND.Proof (d :: shifted Γ) (∃⁰ edge (.fvar (g+1)) (.fvar 0) (.bvar 0)) := by
    apply exsIntro _ (.fvar 0)
    convert he using 1 <;> isoSyntax
  convert impIntro out using 1 <;> (dsimp [d] <;> isoSyntax)

def identityRightTotal {Γ : List Form} (g a : Nat)
    (hg : ND.Proof Γ (identityTotal (.fvar g) (.fvar a))) :
    ND.Proof Γ (graphRightTotal (.fvar g) (.fvar a)) := by
  apply allIntro
  let d : Form := mem (.fvar (a+1)) (.fvar 0)
  have hd : ND.Proof (d :: shifted Γ) d := assumption (by simp)
  have he := identityTotalAt (g+1) (a+1) 0 (up (identityTotalShift g a hg) d) hd
  have out : ND.Proof (d :: shifted Γ) (∃⁰ edge (.fvar (g+1)) (.bvar 0) (.fvar 0)) := by
    apply exsIntro _ (.fvar 0)
    convert he using 1 <;> isoSyntax
  convert impIntro out using 1 <;> (dsimp [d] <;> isoSyntax)

#print axioms identityTyped
#print axioms identityLeftTotal
#print axioms identityRightTotal
end M6.PA.RelationalSource.PairGraph
