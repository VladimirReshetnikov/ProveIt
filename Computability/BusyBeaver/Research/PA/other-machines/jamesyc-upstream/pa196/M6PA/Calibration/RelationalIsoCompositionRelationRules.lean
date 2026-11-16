module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoCompositionEdgesElimination
public import M6PA.Calibration.RelationalOrderIsoRelationRules
public import M6PA.Calibration.RelationalIsoInverseRules
@[expose] public section

/-! Composite relations inherit typing, uniqueness, and order from their
actual component graphs. Ordinary equality aligns intermediate witnesses. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def compositionEdgeTyped {Γ : List Form} (g h a b c x z : Nat)
    (ht : ND.Proof Γ (graphTyped (.fvar g) (.fvar a) (.fvar b)))
    (hu : ND.Proof Γ (graphTyped (.fvar h) (.fvar b) (.fvar c)))
    (he : ND.Proof Γ (compositionEdge (.fvar g) (.fvar h) (.fvar x) (.fvar z))) :
    ND.Proof Γ (mem (.fvar a) (.fvar x) ⋏ mem (.fvar c) (.fvar z)) := by
  apply compositionEdgeEliminate g h x z _ he
  intro Δ inc hg hh
  have hl := orderTypedAt (g+1) (a+1) (b+1) (x+1) 0 (ND.weaken (orderTypedShift g a b ht) inc) hg
  have hr := orderTypedAt (h+1) (b+1) (c+1) 0 (z+1) (ND.weaken (orderTypedShift h b c hu) inc) hh
  convert andIntro (andLeft hl) (andRight hr) using 1 <;> compositionSyntax

def compositionEdgeFunctional {Γ : List Form} (E : FormulaEquality Γ) (g h x z w : Nat)
    (hg : ND.Proof Γ (graphFunctional (.fvar g)))
    (hh : ND.Proof Γ (graphFunctional (.fvar h)))
    (hz : ND.Proof Γ (compositionEdge (.fvar g) (.fvar h) (.fvar x) (.fvar z)))
    (hw : ND.Proof Γ (compositionEdge (.fvar g) (.fvar h) (.fvar x) (.fvar w))) :
    ND.Proof Γ (eq (.fvar z) (.fvar w)) := by
  apply compositionEdgesEliminate g h x z x w _ hz hw
  intro Δ inc hxy hyz hxv hvw
  have gg : ND.Proof Δ (graphFunctional (.fvar (g+1+1))) := by
    convert ND.weaken (shiftProof (shiftProof hg)) inc using 1 <;> compositionSyntax
  have hh' : ND.Proof Δ (graphFunctional (.fvar (h+1+1))) := by
    convert ND.weaken (shiftProof (shiftProof hh)) inc using 1 <;> compositionSyntax
  have ee := E.shifted.shifted.weaken inc
  have hyv := graphFunctionalAt (g+1+1) (x+1+1) 1 0 gg hxy hxv
  have hyw := edgeInputTransport ee (h+1+1) 0 1 (w+1+1) (ee.symmetryOf hyv) hvw
  convert graphFunctionalAt (h+1+1) 1 (z+1+1) (w+1+1) hh' hyz hyw using 1 <;> compositionSyntax

def compositionEdgeInjective {Γ : List Form} (E : FormulaEquality Γ) (g h x u z : Nat)
    (hg : ND.Proof Γ (graphInjective (.fvar g)))
    (hh : ND.Proof Γ (graphInjective (.fvar h)))
    (hx : ND.Proof Γ (compositionEdge (.fvar g) (.fvar h) (.fvar x) (.fvar z)))
    (hu : ND.Proof Γ (compositionEdge (.fvar g) (.fvar h) (.fvar u) (.fvar z))) :
    ND.Proof Γ (eq (.fvar x) (.fvar u)) := by
  apply compositionEdgesEliminate g h x z u z _ hx hu
  intro Δ inc hxy hyz huv hvz
  have gg := ND.weaken (orderInjectiveShift (g+1) (orderInjectiveShift g hg)) inc
  have hh' := ND.weaken (orderInjectiveShift (h+1) (orderInjectiveShift h hh)) inc
  have ee := E.shifted.shifted.weaken inc
  have hyv := orderInjectiveAt (h+1+1) 1 0 (z+1+1) hh' hyz hvz
  have huy := inverseEdgeOutputTransport ee (g+1+1) (u+1+1) 0 1 (ee.symmetryOf hyv) huv
  convert orderInjectiveAt (g+1+1) (x+1+1) (u+1+1) 1 gg hxy huy using 1 <;> compositionSyntax

def compositionEdgeOrder {Γ : List Form} (g h x u z w : Nat)
    (hg : ND.Proof Γ (graphOrder (.fvar g)))
    (hh : ND.Proof Γ (graphOrder (.fvar h)))
    (hx : ND.Proof Γ (compositionEdge (.fvar g) (.fvar h) (.fvar x) (.fvar z)))
    (hu : ND.Proof Γ (compositionEdge (.fvar g) (.fvar h) (.fvar u) (.fvar w))) :
    ND.Proof Γ (sourceIff (mem (.fvar x) (.fvar u)) (mem (.fvar z) (.fvar w))) := by
  apply compositionEdgesEliminate g h x z u w _ hx hu
  intro Δ inc hxy hyz huv hvw
  have gg := ND.weaken (orderOrderShift (g+1) (orderOrderShift g hg)) inc
  have hh' := ND.weaken (orderOrderShift (h+1) (orderOrderShift h hh)) inc
  have h1 := orderOrderAt (g+1+1) (x+1+1) (u+1+1) 1 0 gg hxy huv
  have h2 := orderOrderAt (h+1+1) 1 0 (z+1+1) (w+1+1) hh' hyz hvw
  have out : ND.Proof Δ (sourceIff (mem (.fvar (x+1+1)) (.fvar (u+1+1)))
      (mem (.fvar (z+1+1)) (.fvar (w+1+1)))) := by
    apply andIntro
    · apply impIntro
      exact mp (mp (assumption (by simp)) (up (andLeft h1) _)) (up (andLeft h2) _)
    · apply impIntro
      exact mp (mp (assumption (by simp)) (up (andRight h2) _)) (up (andRight h1) _)
  convert out using 1 <;> compositionSyntax

#print axioms compositionEdgeTyped
#print axioms compositionEdgeFunctional
#print axioms compositionEdgeInjective
#print axioms compositionEdgeOrder
end M6.PA.RelationalSource.PairGraph
