module
public import M6PA.Theory
public import M6PA.Calibration.RelationalAdditionZeroSupplier
@[expose] public section

/-! Finite elimination and equality-transport rules for the literal inclusive
trace clauses. These operate on actual LK proofs, not semantic interfaces. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def outputIntro {Γ : List Form} (g x y : Nat)
    (h : ND.Proof Γ (edge (.fvar g) (.fvar x) (.fvar y))) :
    ND.Proof Γ (hasOutput (.fvar g) (.fvar x)) := by
  apply exsIntro _ (.fvar y)
  convert h using 1 ; traceSyntax

def graphDomainAt {Γ : List Form} (a g x : Nat)
    (h : ND.Proof Γ (graphDomain (.fvar a) (.fvar g))) :
    ND.Proof Γ (sourceIff (hasOutput (.fvar g) (.fvar x))
      (mem (.fvar a) (.fvar x) ⋎ eq (.fvar x) (.fvar a))) := by
  convert allElim _ (.fvar x) h using 1 <;> (dsimp only [hasOutput] <;> traceSyntax)

def graphFunctionalAt {Γ : List Form} (g x y z : Nat)
    (h : ND.Proof Γ (graphFunctional (.fvar g)))
    (hy : ND.Proof Γ (edge (.fvar g) (.fvar x) (.fvar y)))
    (hz : ND.Proof Γ (edge (.fvar g) (.fvar x) (.fvar z))) :
    ND.Proof Γ (eq (.fvar y) (.fvar z)) := by
  have hf : ND.Proof Γ (sourceImply (edge (.fvar g) (.fvar x) (.fvar y) ⋏
      edge (.fvar g) (.fvar x) (.fvar z)) (eq (.fvar y) (.fvar z))) := by
    convert allElim _ (.fvar z) (allElim _ (.fvar y) (allElim _ (.fvar x) h)) using 1
    traceSyntax
  exact mp (andIntro hy hz) hf

def graphRangeAt {Γ : List Form} (g x y : Nat)
    (h : ND.Proof Γ (graphRange (.fvar g)))
    (he : ND.Proof Γ (edge (.fvar g) (.fvar x) (.fvar y))) :
    ND.Proof Γ (Ordinal.domain (.fvar y)) := by
  have hi : ND.Proof Γ (sourceImply (edge (.fvar g) (.fvar x) (.fvar y)) (Ordinal.domain (.fvar y))) := by
    convert allElim _ (.fvar y) (allElim _ (.fvar x) h) using 1 ; traceSyntax
  exact mp he hi

def edgeInputTransport {Γ : List Form} (E : FormulaEquality Γ) (g x u y : Nat)
    (hxu : ND.Proof Γ (eq (.fvar x) (.fvar u)))
    (h : ND.Proof Γ (edge (.fvar g) (.fvar x) (.fvar y))) :
    ND.Proof Γ (edge (.fvar g) (.fvar u) (.fvar y)) := by
  have hp : ND.Proof Γ (Semiformula.rewAux (Rew.subst ![.fvar x]) (edge (.fvar g) (.bvar 0) (.fvar y))) := by
    convert h using 1 ; traceSyntax
  have ht := E.substituteOne (edge (.fvar g) (.bvar 0) (.fvar y)) (.fvar x) (.fvar u) hxu hp
  convert ht using 1 ; traceSyntax

#print axioms graphDomainAt
#print axioms graphFunctionalAt
#print axioms graphRangeAt
#print axioms edgeInputTransport
end M6.PA.RelationalSource.PairGraph
