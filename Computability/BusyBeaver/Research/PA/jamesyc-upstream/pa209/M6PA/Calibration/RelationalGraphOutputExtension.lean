module
public import M6PA.Theory
public import M6PA.Calibration.RelationalGraphOperations
@[expose] public section

/-! Exact output-domain behavior of a genuine graph extension. Existential
outputs are eliminated and constructed explicitly. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)

def exactPreservesEdge {Γ : List Form} (g h a b x y : Nat)
    (hx : ND.Proof Γ (exactExtension (.fvar g) (.fvar h) (.fvar a) (.fvar b)))
    (he : ND.Proof Γ (edge (.fvar g) (.fvar x) (.fvar y))) :
    ND.Proof Γ (edge (.fvar h) (.fvar x) (.fvar y)) :=
  mp (ND.orLeft he) (andRight (exactAt g h a b x y hx))

def outputExtensionForward {Γ : List Form} (g h a b x : Nat)
    (hx : ND.Proof Γ (exactExtension (.fvar g) (.fvar h) (.fvar a) (.fvar b)))
    (he : ND.Proof Γ (hasOutput (.fvar h) (.fvar x))) :
    ND.Proof Γ (hasOutput (.fvar g) (.fvar x) ⋎ eq (.fvar x) (.fvar a)) := by
  apply exsElim he
  let σ : Formula 1 := edge (.fvar h) (.fvar x) (.bvar 0)
  let C := σ.free :: shifted Γ
  have hh : ND.Proof C (edge (.fvar (h+1)) (.fvar (x+1)) (.fvar 0)) := by
    have ht : ND.Proof C σ.free := assumption (by simp [C])
    convert ht using 1 ; dsimp [σ]; traceSyntax
  have hc := mp hh (andLeft (exactAt (g+1) (h+1) (a+1) (b+1) (x+1) 0
    (up (exactShift g h a b hx) σ.free)))
  have out : ND.Proof C (hasOutput (.fvar (g+1)) (.fvar (x+1)) ⋎ eq (.fvar (x+1)) (.fvar (a+1))) := by
    apply orElim hc
    · exact ND.orLeft (outputIntro (g+1) (x+1) 0 (assumption (by simp)))
    · exact ND.orRight (andLeft (assumption (p := eq (.fvar (x+1)) (.fvar (a+1)) ⋏ eq (.fvar 0) (.fvar (b+1))) (by simp)))
  convert out using 1 <;> (dsimp [C,σ,hasOutput] <;> traceSyntax)

def preservesOutput {Γ : List Form} (g h a b x : Nat)
    (hx : ND.Proof Γ (exactExtension (.fvar g) (.fvar h) (.fvar a) (.fvar b)))
    (he : ND.Proof Γ (hasOutput (.fvar g) (.fvar x))) :
    ND.Proof Γ (hasOutput (.fvar h) (.fvar x)) := by
  apply exsElim he
  let σ : Formula 1 := edge (.fvar g) (.fvar x) (.bvar 0)
  let C := σ.free :: shifted Γ
  have hh : ND.Proof C (edge (.fvar (g+1)) (.fvar (x+1)) (.fvar 0)) := by
    have ht : ND.Proof C σ.free := assumption (by simp [C])
    convert ht using 1 ; dsimp [σ]; traceSyntax
  have hp := exactPreservesEdge (g+1) (h+1) (a+1) (b+1) (x+1) 0
    (up (exactShift g h a b hx) σ.free) hh
  have out := outputIntro (h+1) (x+1) 0 hp
  convert out using 1 <;> (dsimp [C,σ,hasOutput] <;> traceSyntax)

def insertedOutput {Γ : List Form} (E : FormulaEquality Γ) (g h a b x : Nat)
    (hx : ND.Proof Γ (exactExtension (.fvar g) (.fvar h) (.fvar a) (.fvar b)))
    (he : ND.Proof Γ (eq (.fvar x) (.fvar a))) :
    ND.Proof Γ (hasOutput (.fvar h) (.fvar x)) := by
  have hp := mp (ND.orRight (andIntro he (E.reflexive (.fvar b)))) (andRight (exactAt g h a b x b hx))
  exact outputIntro h x b hp

#print axioms outputExtensionForward
#print axioms preservesOutput
#print axioms insertedOutput
end M6.PA.RelationalSource.PairGraph
