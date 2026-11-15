import PA194FoundationCompositionEdge
import PA194FoundationInverseOrderRules
set_option maxHeartbeats 8000000

/-! Source graph totality provides real intermediate and output witnesses. -/
namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND
open Ordinal (Term Formula)

def compositionOutputFromIntermediate {Γ : List Form} (g h x y : Nat)
    (hg : ND.Proof Γ (edge (.fvar g) (.fvar x) (.fvar y)))
    (hh : ND.Proof Γ (∃⁰ edge (.fvar h) (.fvar y) (.bvar 0))) :
    ND.Proof Γ (∃⁰ compositionEdge (.fvar g) (.fvar h) (.fvar x) (.bvar 0)) := by
  apply exsElim hh
  let σ : Formula 1 := edge (.fvar h) (.fvar y) (.bvar 0)
  let C := σ.free :: shifted Γ
  have hh : ND.Proof C (edge (.fvar (h+1)) (.fvar (y+1)) (.fvar 0)) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [σ] <;> compositionSyntax)
  have gg : ND.Proof C (edge (.fvar (g+1)) (.fvar (x+1)) (.fvar (y+1))) := by
    convert up (shiftProof hg) σ.free using 1 <;> compositionSyntax
  have out : ND.Proof C (∃⁰ compositionEdge (.fvar (g+1)) (.fvar (h+1)) (.fvar (x+1)) (.bvar 0)) := by
    apply exsIntro _ (.fvar 0)
    convert compositionEdgeIntro (g+1) (h+1) (x+1) (y+1) 0 gg hh using 1 <;> compositionSyntax
  convert out using 1 <;> (dsimp [C,σ] <;> compositionSyntax)

def compositionOutputAt {Γ : List Form} (g h a b x : Nat)
    (ht : ND.Proof Γ (graphTyped (.fvar g) (.fvar a) (.fvar b)))
    (hg : ND.Proof Γ (graphLeftTotal (.fvar g) (.fvar a)))
    (hh : ND.Proof Γ (graphLeftTotal (.fvar h) (.fvar b)))
    (hx : ND.Proof Γ (mem (.fvar a) (.fvar x))) :
    ND.Proof Γ (∃⁰ compositionEdge (.fvar g) (.fvar h) (.fvar x) (.bvar 0)) := by
  apply exsElim (inverseOrderLeftAt g a x hg hx)
  let σ : Formula 1 := edge (.fvar g) (.fvar x) (.bvar 0)
  let C := σ.free :: shifted Γ
  have gg : ND.Proof C (edge (.fvar (g+1)) (.fvar (x+1)) (.fvar 0)) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [σ] <;> compositionSyntax)
  have hy := andRight (inverseOrderTypedAt (g+1) (a+1) (b+1) (x+1) 0 (up (inverseOrderTypedShift g a b ht) σ.free) gg)
  have hz := inverseOrderLeftAt (h+1) (b+1) 0 (up (inverseOrderLeftShift h b hh) σ.free) hy
  have out := compositionOutputFromIntermediate (g+1) (h+1) (x+1) 0 gg hz
  convert out using 1 <;> (dsimp [C,σ] <;> compositionSyntax)

#print axioms compositionOutputFromIntermediate
#print axioms compositionOutputAt
end M6.PA.RelationalSource.PairGraph
