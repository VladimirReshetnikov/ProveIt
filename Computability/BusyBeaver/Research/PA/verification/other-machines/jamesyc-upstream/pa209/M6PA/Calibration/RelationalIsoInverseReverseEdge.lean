module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoInverseBijectionRules
@[expose] public section

/-! Existential coverage and forward functionality recover every reversed edge. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)

def inverseReverseEdge {Γ : List Form} (E : FormulaEquality Γ) (g a h x y : Nat)
    (hf : ND.Proof Γ (graphFunctional (.fvar g)))
    (hc : ND.Proof Γ (inverseCoverage (.fvar g) (.fvar a) (.fvar h)))
    (hm : ND.Proof Γ (mem (.fvar a) (.fvar x)))
    (he : ND.Proof Γ (edge (.fvar g) (.fvar x) (.fvar y))) :
    ND.Proof Γ (edge (.fvar h) (.fvar y) (.fvar x)) := by
  apply exsElim (inverseCoverageAt g a h x hc hm)
  let σ : Formula 1 := edge (.fvar h) (.bvar 0) (.fvar x) ⋏ edge (.fvar g) (.fvar x) (.bvar 0)
  let C := σ.free :: shifted Γ
  have hh : ND.Proof C (edge (.fvar (h+1)) (.fvar 0) (.fvar (x+1)) ⋏
      edge (.fvar (g+1)) (.fvar (x+1)) (.fvar 0)) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [σ] <;> inverseSyntax)
  have ff : ND.Proof C (graphFunctional (.fvar (g+1))) := by
    convert up (shiftProof hf) σ.free using 1 <;> inverseSyntax
  have ee : ND.Proof C (edge (.fvar (g+1)) (.fvar (x+1)) (.fvar (y+1))) := by
    convert up (shiftProof he) σ.free using 1 <;> inverseSyntax
  have hy := graphFunctionalAt (g+1) (x+1) 0 (y+1) ff (andRight hh) ee
  have out := edgeInputTransport (E.shifted.weaken (fun p hp => List.mem_cons_of_mem σ.free hp))
    (h+1) 0 (y+1) (x+1) hy (andLeft hh)
  convert out using 1 <;> (dsimp [C,σ] <;> inverseSyntax)

#print axioms inverseReverseEdge
end M6.PA.RelationalSource.PairGraph
