import PA194FoundationCompositionEdge
import PA194FoundationInverseOrderRules
set_option maxHeartbeats 8000000

/-! Actual right-totality witnesses for the composite relation. -/
namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND
open Ordinal (Term Formula)

def compositionInputFromIntermediate {Γ : List Form} (g h y z : Nat)
    (hh : ND.Proof Γ (edge (.fvar h) (.fvar y) (.fvar z)))
    (hg : ND.Proof Γ (∃⁰ edge (.fvar g) (.bvar 0) (.fvar y))) :
    ND.Proof Γ (∃⁰ compositionEdge (.fvar g) (.fvar h) (.bvar 0) (.fvar z)) := by
  apply exsElim hg
  let σ : Formula 1 := edge (.fvar g) (.bvar 0) (.fvar y)
  let C := σ.free :: shifted Γ
  have gg : ND.Proof C (edge (.fvar (g+1)) (.fvar 0) (.fvar (y+1))) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [σ] <;> compositionSyntax)
  have hh' : ND.Proof C (edge (.fvar (h+1)) (.fvar (y+1)) (.fvar (z+1))) := by
    convert up (shiftProof hh) σ.free using 1 <;> compositionSyntax
  have out : ND.Proof C (∃⁰ compositionEdge (.fvar (g+1)) (.fvar (h+1)) (.bvar 0) (.fvar (z+1))) := by
    apply exsIntro _ (.fvar 0)
    convert compositionEdgeIntro (g+1) (h+1) 0 (y+1) (z+1) gg hh' using 1 <;> compositionSyntax
  convert out using 1 <;> (dsimp [C,σ] <;> compositionSyntax)

def compositionInputAt {Γ : List Form} (g h b c z : Nat)
    (ht : ND.Proof Γ (graphTyped (.fvar h) (.fvar b) (.fvar c)))
    (hg : ND.Proof Γ (graphRightTotal (.fvar g) (.fvar b)))
    (hh : ND.Proof Γ (graphRightTotal (.fvar h) (.fvar c)))
    (hz : ND.Proof Γ (mem (.fvar c) (.fvar z))) :
    ND.Proof Γ (∃⁰ compositionEdge (.fvar g) (.fvar h) (.bvar 0) (.fvar z)) := by
  apply exsElim (inverseOrderRightAt h c z hh hz)
  let σ : Formula 1 := edge (.fvar h) (.bvar 0) (.fvar z)
  let C := σ.free :: shifted Γ
  have hh' : ND.Proof C (edge (.fvar (h+1)) (.fvar 0) (.fvar (z+1))) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [σ] <;> compositionSyntax)
  have hy := andLeft (inverseOrderTypedAt (h+1) (b+1) (c+1) 0 (z+1) (up (inverseOrderTypedShift h b c ht) σ.free) hh')
  have hx := inverseOrderRightAt (g+1) (b+1) 0 (up (inverseOrderRightShift g b hg) σ.free) hy
  have out := compositionInputFromIntermediate (g+1) (h+1) 0 (z+1) hh' hx
  convert out using 1 <;> (dsimp [C,σ] <;> compositionSyntax)

#print axioms compositionInputFromIntermediate
#print axioms compositionInputAt
end M6.PA.RelationalSource.PairGraph
