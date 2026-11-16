module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoCompositionPrefix
public import M6PA.Calibration.RelationalGraphOperations
@[expose] public section

/-! Finite introduction/elimination for a relational composite edge. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)

def compositionEdgeIntro {Γ : List Form} (g h x y z : Nat)
    (hg : ND.Proof Γ (edge (.fvar g) (.fvar x) (.fvar y)))
    (hh : ND.Proof Γ (edge (.fvar h) (.fvar y) (.fvar z))) :
    ND.Proof Γ (compositionEdge (.fvar g) (.fvar h) (.fvar x) (.fvar z)) := by
  apply exsIntro _ (.fvar y)
  convert andIntro hg hh using 1 <;> compositionSyntax

def compositionEdgeEliminate {Γ : List Form} (g h x z : Nat) (q : Form)
    (he : ND.Proof Γ (compositionEdge (.fvar g) (.fvar h) (.fvar x) (.fvar z)))
    (k : ∀ {Δ : List Form}, (∀ p, p ∈ shifted Γ → p ∈ Δ) →
      ND.Proof Δ (edge (.fvar (g+1)) (.fvar (x+1)) (.fvar 0)) →
      ND.Proof Δ (edge (.fvar (h+1)) (.fvar 0) (.fvar (z+1))) → ND.Proof Δ q.shift) :
    ND.Proof Γ q := by
  apply exsElim he
  let σ : Formula 1 := edge (.fvar g) (.fvar x) (.bvar 0) ⋏ edge (.fvar h) (.bvar 0) (.fvar z)
  let C := σ.free :: shifted Γ
  have hh : ND.Proof C (edge (.fvar (g+1)) (.fvar (x+1)) (.fvar 0) ⋏
      edge (.fvar (h+1)) (.fvar 0) (.fvar (z+1))) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [σ] <;> compositionSyntax)
  exact k (fun p hp => List.mem_cons_of_mem σ.free hp) (andLeft hh) (andRight hh)

def compositionEdgeInputTransport {Γ : List Form} (E : FormulaEquality Γ) (g h x z u : Nat)
    (hx : ND.Proof Γ (eq (.fvar x) (.fvar u)))
    (he : ND.Proof Γ (compositionEdge (.fvar g) (.fvar h) (.fvar x) (.fvar z))) :
    ND.Proof Γ (compositionEdge (.fvar g) (.fvar h) (.fvar u) (.fvar z)) := by
  have hp : ND.Proof Γ (Semiformula.rewAux (Rew.subst ![.fvar x])
      (compositionEdge (.fvar g) (.fvar h) (.bvar 0) (.fvar z))) := by
    convert he using 1 <;> compositionSyntax
  have ht := E.substituteOne (compositionEdge (.fvar g) (.fvar h) (.bvar 0) (.fvar z))
    (.fvar x) (.fvar u) hx hp
  convert ht using 1 <;> compositionSyntax

def compositionEdgeOutputTransport {Γ : List Form} (E : FormulaEquality Γ) (g h x z w : Nat)
    (hz : ND.Proof Γ (eq (.fvar z) (.fvar w)))
    (he : ND.Proof Γ (compositionEdge (.fvar g) (.fvar h) (.fvar x) (.fvar z))) :
    ND.Proof Γ (compositionEdge (.fvar g) (.fvar h) (.fvar x) (.fvar w)) := by
  have hp : ND.Proof Γ (Semiformula.rewAux (Rew.subst ![.fvar z])
      (compositionEdge (.fvar g) (.fvar h) (.fvar x) (.bvar 0))) := by
    convert he using 1 <;> compositionSyntax
  have ht := E.substituteOne (compositionEdge (.fvar g) (.fvar h) (.fvar x) (.bvar 0))
    (.fvar z) (.fvar w) hz hp
  convert ht using 1 <;> compositionSyntax

#print axioms compositionEdgeIntro
#print axioms compositionEdgeEliminate
#print axioms compositionEdgeInputTransport
#print axioms compositionEdgeOutputTransport
end M6.PA.RelationalSource.PairGraph
