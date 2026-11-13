module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoCompositionRelationRules
public import M6PA.Calibration.RelationalIsoCompositionRules
@[expose] public section

/-! Coverage and component functionality recover every composite edge in the
actual constructed graph, without assuming a comprehension/image object. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)

def compositionRealizeEdge {Γ : List Form} (E : FormulaEquality Γ) (g h a k x z : Nat)
    (fg : ND.Proof Γ (graphFunctional (.fvar g)))
    (fh : ND.Proof Γ (graphFunctional (.fvar h)))
    (hc : ND.Proof Γ (compositionCoverage (.fvar g) (.fvar h) (.fvar a) (.fvar k)))
    (hm : ND.Proof Γ (mem (.fvar a) (.fvar x)))
    (he : ND.Proof Γ (compositionEdge (.fvar g) (.fvar h) (.fvar x) (.fvar z))) :
    ND.Proof Γ (edge (.fvar k) (.fvar x) (.fvar z)) := by
  apply exsElim (compositionCoverageAt g h a k x hc hm)
  let σ : Formula 1 := edge (.fvar k) (.fvar x) (.bvar 0) ⋏ compositionEdge (.fvar g) (.fvar h) (.fvar x) (.bvar 0)
  let C := σ.free :: shifted Γ
  have hh : ND.Proof C (edge (.fvar (k+1)) (.fvar (x+1)) (.fvar 0) ⋏
      compositionEdge (.fvar (g+1)) (.fvar (h+1)) (.fvar (x+1)) (.fvar 0)) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [σ] <;> compositionSyntax)
  have gg : ND.Proof C (graphFunctional (.fvar (g+1))) := by
    convert up (shiftProof fg) σ.free using 1 <;> compositionSyntax
  have ff : ND.Proof C (graphFunctional (.fvar (h+1))) := by
    convert up (shiftProof fh) σ.free using 1 <;> compositionSyntax
  have ee : ND.Proof C (compositionEdge (.fvar (g+1)) (.fvar (h+1)) (.fvar (x+1)) (.fvar (z+1))) := by
    convert up (shiftProof he) σ.free using 1 <;> compositionSyntax
  have E' := E.shifted.weaken (fun p hp => List.mem_cons_of_mem σ.free hp)
  have hz := compositionEdgeFunctional E' (g+1) (h+1) (x+1) 0 (z+1) gg ff (andRight hh) ee
  have out := inverseEdgeOutputTransport E' (k+1) (x+1) 0 (z+1) hz (andLeft hh)
  convert out using 1 <;> (dsimp [C,σ] <;> compositionSyntax)

#print axioms compositionRealizeEdge
end M6.PA.RelationalSource.PairGraph
