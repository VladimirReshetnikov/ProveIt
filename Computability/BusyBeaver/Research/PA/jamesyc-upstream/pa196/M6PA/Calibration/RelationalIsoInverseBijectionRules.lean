module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoInverseRules
public import M6PA.Calibration.RelationalOrderIsoRelationRules
@[expose] public section

/-! Reversal exchanges functionality with injectivity and reverses the
order biconditional. All statements concern the displayed finite graphs. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def inverseTypedAt {Γ : List Form} (g a b h y x : Nat)
    (ht : ND.Proof Γ (graphTyped (.fvar g) (.fvar a) (.fvar b)))
    (hc : ND.Proof Γ (inverseCorrect (.fvar g) (.fvar a) (.fvar h)))
    (he : ND.Proof Γ (edge (.fvar h) (.fvar y) (.fvar x))) :
    ND.Proof Γ (mem (.fvar b) (.fvar y) ⋏ mem (.fvar a) (.fvar x)) := by
  have hh := inverseCorrectAt g a h y x hc he
  exact andIntro (andRight (orderTypedAt g a b x y ht (andRight hh))) (andLeft hh)

def inverseFunctionalAt {Γ : List Form} (g a h y x u : Nat)
    (hi : ND.Proof Γ (graphInjective (.fvar g)))
    (hc : ND.Proof Γ (inverseCorrect (.fvar g) (.fvar a) (.fvar h)))
    (hx : ND.Proof Γ (edge (.fvar h) (.fvar y) (.fvar x)))
    (hu : ND.Proof Γ (edge (.fvar h) (.fvar y) (.fvar u))) :
    ND.Proof Γ (eq (.fvar x) (.fvar u)) :=
  orderInjectiveAt g x u y hi (andRight (inverseCorrectAt g a h y x hc hx))
    (andRight (inverseCorrectAt g a h y u hc hu))

def inverseInjectiveAt {Γ : List Form} (g a h y v x : Nat)
    (hf : ND.Proof Γ (graphFunctional (.fvar g)))
    (hc : ND.Proof Γ (inverseCorrect (.fvar g) (.fvar a) (.fvar h)))
    (hy : ND.Proof Γ (edge (.fvar h) (.fvar y) (.fvar x)))
    (hv : ND.Proof Γ (edge (.fvar h) (.fvar v) (.fvar x))) :
    ND.Proof Γ (eq (.fvar y) (.fvar v)) :=
  graphFunctionalAt g x y v hf (andRight (inverseCorrectAt g a h y x hc hy))
    (andRight (inverseCorrectAt g a h v x hc hv))

def inverseOrderAt {Γ : List Form} (g a h y v x u : Nat)
    (ho : ND.Proof Γ (graphOrder (.fvar g)))
    (hc : ND.Proof Γ (inverseCorrect (.fvar g) (.fvar a) (.fvar h)))
    (hy : ND.Proof Γ (edge (.fvar h) (.fvar y) (.fvar x)))
    (hv : ND.Proof Γ (edge (.fvar h) (.fvar v) (.fvar u))) :
    ND.Proof Γ (sourceIff (mem (.fvar y) (.fvar v)) (mem (.fvar x) (.fvar u))) := by
  have hh := orderOrderAt g x u y v ho (andRight (inverseCorrectAt g a h y x hc hy))
    (andRight (inverseCorrectAt g a h v u hc hv))
  exact andIntro (andRight hh) (andLeft hh)

#print axioms inverseTypedAt
#print axioms inverseFunctionalAt
#print axioms inverseInjectiveAt
#print axioms inverseOrderAt
end M6.PA.RelationalSource.PairGraph
