module
public import M6PA.Theory
public import M6PA.Calibration.RelationalGraphRangeExtension
public import M6PA.Calibration.RelationalGraphFunctionalExtension
@[expose] public section

/-! Finite recurrence elimination and transport for the literal first-argument
addition graph. Existential previous outputs are real graph members. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)

def addPrevious (g x y : Term n) : Formula n :=
  ∃¹ (edge (Rew.bShift g) (Rew.bShift x) (.bvar 0) ⋏ Ordinal.successor (.bvar 0) (Rew.bShift y))

macro "previousSyntax" : tactic => `(tactic|
  (simp only [addPrevious,addPrefixExists,addPrefix,addRecurrence,addResult,Ordinal.successor,graphDomain,graphFunctional,graphRange,pointGraph,edge,inclusion,
    kuratowskiExists,adjunction,singleton,pair,kuratowski,mem,eq,sourceIff,sourceImply,
    Ordinal.zero,Ordinal.subset,Ordinal.transitive,Ordinal.memberTransitive,Ordinal.memberLinear,
    Ordinal.nonempty,Ordinal.least,Ordinal.greatest,Ordinal.internalExtrema,Ordinal.representative,
    Ordinal.memberIr,Ordinal.domain,
    Semiformula.shift,Semiformula.free,Rewriting.shift,Rewriting.free,Rewriting.subst,
    app_eq_rewAux,Semiformula.rewAux,Semiformula.neg,Semiformula.imp_eq,Semiformula.neg_eq];
    finishSourceSyntax))

def recurrenceAt {Γ : List Form} (g x y z : Nat)
    (hr : ND.Proof Γ (addRecurrence (.fvar g)))
    (he : ND.Proof Γ (edge (.fvar g) (.fvar x) (.fvar y)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar z) (.fvar x))) :
    ND.Proof Γ (addPrevious (.fvar g) (.fvar z) (.fvar y)) := by
  have hi : ND.Proof Γ (sourceImply (edge (.fvar g) (.fvar x) (.fvar y) ⋏
      Ordinal.successor (.fvar z) (.fvar x)) (addPrevious (.fvar g) (.fvar z) (.fvar y))) := by
    convert allElim _ (.fvar z) (allElim _ (.fvar y) (allElim _ (.fvar x) hr)) using 1
    previousSyntax
  exact mp (andIntro he hs) hi

def previousIntro {Γ : List Form} (g x y w : Nat)
    (he : ND.Proof Γ (edge (.fvar g) (.fvar x) (.fvar w)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar w) (.fvar y))) :
    ND.Proof Γ (addPrevious (.fvar g) (.fvar x) (.fvar y)) := by
  apply exsIntro _ (.fvar w)
  convert andIntro he hs using 1 ; previousSyntax

def preservePrevious {Γ : List Form} (g h a b x y : Nat)
    (hx : ND.Proof Γ (exactExtension (.fvar g) (.fvar h) (.fvar a) (.fvar b)))
    (hp : ND.Proof Γ (addPrevious (.fvar g) (.fvar x) (.fvar y))) :
    ND.Proof Γ (addPrevious (.fvar h) (.fvar x) (.fvar y)) := by
  apply exsElim hp
  let σ : Formula 1 := edge (.fvar g) (.fvar x) (.bvar 0) ⋏ Ordinal.successor (.bvar 0) (.fvar y)
  let C := σ.free :: shifted Γ
  have hc : ND.Proof C (edge (.fvar (g+1)) (.fvar (x+1)) (.fvar 0) ⋏
      Ordinal.successor (.fvar 0) (.fvar (y+1))) := by
    have h0 : ND.Proof C σ.free := assumption (by simp [C])
    convert h0 using 1 ; dsimp [σ]; previousSyntax
  have he := exactPreservesEdge (g+1) (h+1) (a+1) (b+1) (x+1) 0
    (up (exactShift g h a b hx) σ.free) (andLeft hc)
  have out := previousIntro (h+1) (x+1) (y+1) 0 he (andRight hc)
  convert out using 1 <;> (dsimp [C,σ] <;> previousSyntax)

def successorTargetTransport {Γ : List Form} (E : FormulaEquality Γ) (a b c : Nat)
    (hbc : ND.Proof Γ (eq (.fvar b) (.fvar c)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar a) (.fvar b))) :
    ND.Proof Γ (Ordinal.successor (.fvar a) (.fvar c)) := by
  have hp : ND.Proof Γ (Semiformula.rewAux (Rew.subst ![.fvar b]) (Ordinal.successor (.fvar a) (.bvar 0))) := by
    convert hs using 1 ; successorSyntax
  have out := E.substituteOne (Ordinal.successor (.fvar a) (.bvar 0)) (.fvar b) (.fvar c) hbc hp
  convert out using 1 ; successorSyntax

#print axioms recurrenceAt
#print axioms preservePrevious
#print axioms successorTargetTransport
end M6.PA.RelationalSource.PairGraph
