module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoCompositionExistsSyntax
public import M6PA.Calibration.RelationalIsoCompositionInduction
@[expose] public section

/-! Construct an actual composite order-isomorphism from two displayed
bijections. The precise Separation instance is explicit at this layer. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)

set_option maxHeartbeats 800000 in
def compositionIsoFromPrefix {Γ : List Form} (E : FormulaEquality Γ) (g h a b c : Nat)
    (hg : ND.Proof Γ (orderBijection (.fvar g) (.fvar a) (.fvar b)))
    (hh : ND.Proof Γ (orderBijection (.fvar h) (.fvar b) (.fvar c)))
    (hk : ND.Proof Γ (compositionPrefixExists (.fvar g) (.fvar h) (.fvar a))) :
    ND.Proof Γ (orderIso (.fvar a) (.fvar c)) := by
  apply exsElim hk
  let σ : Formula 1 := compositionPrefix (.fvar g) (.fvar h) (.fvar a) (.bvar 0)
  let C := σ.free :: shifted Γ
  have kk : ND.Proof C (compositionPrefix (.fvar (g+1)) (.fvar (h+1)) (.fvar (a+1)) (.fvar 0)) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    simpa only [σ, compositionPrefixFreeEq] using hh
  have gg : ND.Proof C (orderBijection (.fvar (g+1)) (.fvar (a+1)) (.fvar (b+1))) := by
    simpa only [compositionBijectionShiftEq] using up (shiftProof hg) σ.free
  have hh' : ND.Proof C (orderBijection (.fvar (h+1)) (.fvar (b+1)) (.fvar (c+1))) := by
    simpa only [compositionBijectionShiftEq] using up (shiftProof hh) σ.free
  have hb := compositionBijection (E.shifted.weaken (fun p hp => List.mem_cons_of_mem σ.free hp))
    (g+1) (h+1) (a+1) (b+1) (c+1) 0 gg hh' kk
  have out : ND.Proof C (orderIso (.fvar (a+1)) (.fvar (c+1))) := compositionIsoIntro 0 (a+1) (c+1) hb
  simpa only [C,σ,Rew.bShift_fvar,compositionIsoShiftEq] using out

def compositionIsoOfBijections {Γ : List Form} (E : FormulaEquality Γ) (g h a b c : Nat)
    (hempty : ND.Proof Γ emptyFormula) (hadj : ND.Proof Γ adjunctionFormula)
    (hi : ND.Proof Γ Ordinal.intersectionFormula)
    (hsep : ND.Proof Γ (separationFormula (∼compositionProperty g h a)))
    (hg : ND.Proof Γ (orderBijection (.fvar g) (.fvar a) (.fvar b)))
    (hh : ND.Proof Γ (orderBijection (.fvar h) (.fvar b) (.fvar c)))
    (hd : ND.Proof Γ (Ordinal.domain (.fvar a))) :
    ND.Proof Γ (orderIso (.fvar a) (.fvar c)) :=
  compositionIsoFromPrefix E g h a b c hg hh
    (compositionFullPrefixExists E g h a b hempty hadj hi hsep (andLeft (andRight hg))
      (andLeft (andRight (andRight hg))) (andLeft (andRight (andRight hh))) hd)

#print axioms compositionIsoFromPrefix
#print axioms compositionIsoOfBijections
end M6.PA.RelationalSource.PairGraph
