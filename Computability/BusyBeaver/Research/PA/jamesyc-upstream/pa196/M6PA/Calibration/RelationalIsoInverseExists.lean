module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoInverseBijection
public import M6PA.Calibration.RelationalIsoInverseInduction
@[expose] public section

/-! Construct a reversed order-isomorphism from an actual forward bijection.
The exact parameterized Separation instance remains explicit at this layer. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)

set_option maxHeartbeats 800000 in
def inverseIsoFromPrefix {Γ : List Form} (E : FormulaEquality Γ) (g a b : Nat)
    (hg : ND.Proof Γ (orderBijection (.fvar g) (.fvar a) (.fvar b)))
    (hi : ND.Proof Γ (inversePrefixExists (.fvar g) (.fvar a))) :
    ND.Proof Γ (orderIso (.fvar b) (.fvar a)) := by
  apply exsElim hi
  let σ : Formula 1 := inversePrefix (.fvar g) (.fvar a) (.bvar 0)
  let C := σ.free :: shifted Γ
  have hh : ND.Proof C (inversePrefix (.fvar (g+1)) (.fvar (a+1)) (.fvar 0)) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [σ] <;> inverseSyntax)
  have gg : ND.Proof C (orderBijection (.fvar (g+1)) (.fvar (a+1)) (.fvar (b+1))) := by
    convert up (shiftProof hg) σ.free using 1 <;> inverseSyntax
  have hb := inverseBijection (E.shifted.weaken (fun p hp => List.mem_cons_of_mem σ.free hp))
    (g+1) (a+1) (b+1) 0 gg hh
  have out : ND.Proof C (orderIso (.fvar (b+1)) (.fvar (a+1))) := by
    apply exsIntro _ (.fvar 0)
    convert hb using 1 <;> inverseSyntax
  convert out using 1 <;> (dsimp [C,σ] <;> inverseSyntax)

def inverseIsoOfBijection {Γ : List Form} (E : FormulaEquality Γ) (g a b : Nat)
    (hempty : ND.Proof Γ emptyFormula) (hadj : ND.Proof Γ adjunctionFormula)
    (hi : ND.Proof Γ Ordinal.intersectionFormula)
    (hsep : ND.Proof Γ (separationFormula (∼inverseProperty g a)))
    (hg : ND.Proof Γ (orderBijection (.fvar g) (.fvar a) (.fvar b)))
    (hd : ND.Proof Γ (Ordinal.domain (.fvar a))) :
    ND.Proof Γ (orderIso (.fvar b) (.fvar a)) :=
  inverseIsoFromPrefix E g a b hg
    (inverseFullPrefixExists E g a hempty hadj hi hsep (andLeft (andRight (andRight hg))) hd)

#print axioms inverseIsoFromPrefix
#print axioms inverseIsoOfBijection
end M6.PA.RelationalSource.PairGraph
