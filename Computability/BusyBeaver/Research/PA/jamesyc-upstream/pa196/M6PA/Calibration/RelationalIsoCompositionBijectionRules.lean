module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoCompositionRelationRules
public import M6PA.Calibration.RelationalIsoCompositionRules
@[expose] public section

/-! Pointwise typing, uniqueness, and order for the actual composite graph. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def compositionTypedAt {Γ : List Form} (g h a b c k x z : Nat)
    (ht : ND.Proof Γ (graphTyped (.fvar g) (.fvar a) (.fvar b)))
    (hu : ND.Proof Γ (graphTyped (.fvar h) (.fvar b) (.fvar c)))
    (hc : ND.Proof Γ (compositionCorrect (.fvar g) (.fvar h) (.fvar a) (.fvar k)))
    (he : ND.Proof Γ (edge (.fvar k) (.fvar x) (.fvar z))) :
    ND.Proof Γ (mem (.fvar a) (.fvar x) ⋏ mem (.fvar c) (.fvar z)) :=
  compositionEdgeTyped g h a b c x z ht hu (andRight (compositionCorrectAt g h a k x z hc he))

def compositionFunctionalAt {Γ : List Form} (E : FormulaEquality Γ) (g h a k x z w : Nat)
    (hg : ND.Proof Γ (graphFunctional (.fvar g)))
    (hh : ND.Proof Γ (graphFunctional (.fvar h)))
    (hc : ND.Proof Γ (compositionCorrect (.fvar g) (.fvar h) (.fvar a) (.fvar k)))
    (hz : ND.Proof Γ (edge (.fvar k) (.fvar x) (.fvar z)))
    (hw : ND.Proof Γ (edge (.fvar k) (.fvar x) (.fvar w))) :
    ND.Proof Γ (eq (.fvar z) (.fvar w)) :=
  compositionEdgeFunctional E g h x z w hg hh (andRight (compositionCorrectAt g h a k x z hc hz))
    (andRight (compositionCorrectAt g h a k x w hc hw))

def compositionInjectiveAt {Γ : List Form} (E : FormulaEquality Γ) (g h a k x u z : Nat)
    (hg : ND.Proof Γ (graphInjective (.fvar g)))
    (hh : ND.Proof Γ (graphInjective (.fvar h)))
    (hc : ND.Proof Γ (compositionCorrect (.fvar g) (.fvar h) (.fvar a) (.fvar k)))
    (hx : ND.Proof Γ (edge (.fvar k) (.fvar x) (.fvar z)))
    (hu : ND.Proof Γ (edge (.fvar k) (.fvar u) (.fvar z))) :
    ND.Proof Γ (eq (.fvar x) (.fvar u)) :=
  compositionEdgeInjective E g h x u z hg hh (andRight (compositionCorrectAt g h a k x z hc hx))
    (andRight (compositionCorrectAt g h a k u z hc hu))

def compositionOrderAt {Γ : List Form} (g h a k x u z w : Nat)
    (hg : ND.Proof Γ (graphOrder (.fvar g)))
    (hh : ND.Proof Γ (graphOrder (.fvar h)))
    (hc : ND.Proof Γ (compositionCorrect (.fvar g) (.fvar h) (.fvar a) (.fvar k)))
    (hx : ND.Proof Γ (edge (.fvar k) (.fvar x) (.fvar z)))
    (hu : ND.Proof Γ (edge (.fvar k) (.fvar u) (.fvar w))) :
    ND.Proof Γ (sourceIff (mem (.fvar x) (.fvar u)) (mem (.fvar z) (.fvar w))) :=
  compositionEdgeOrder g h x u z w hg hh (andRight (compositionCorrectAt g h a k x z hc hx))
    (andRight (compositionCorrectAt g h a k u w hc hu))

#print axioms compositionTypedAt
#print axioms compositionFunctionalAt
#print axioms compositionInjectiveAt
#print axioms compositionOrderAt
end M6.PA.RelationalSource.PairGraph
