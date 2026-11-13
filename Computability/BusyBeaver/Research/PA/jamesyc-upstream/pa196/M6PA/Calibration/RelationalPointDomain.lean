module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPointGraph
@[expose] public section

/-! The inclusive domain of a point graph at an actual empty ordinal is exactly
that ordinal plus its endpoint. Both existential directions are finite proofs. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)

def hasOutput (g x : Term n) : Formula n :=
  ∃¹ edge (Rew.bShift g) (Rew.bShift x) (.bvar 0)

def pointOutputForward {Γ : List Form} (a b g x : Nat)
    (hp : ND.Proof Γ (pointGraph (.fvar a) (.fvar b) (.fvar g)))
    (he : ND.Proof Γ (hasOutput (.fvar g) (.fvar x))) :
    ND.Proof Γ (eq (.fvar x) (.fvar a)) := by
  apply exsElim he
  let σ : Formula 1 := edge (.fvar g) (.fvar x) (.bvar 0)
  let C := σ.free :: shifted Γ
  have hh : ND.Proof C (edge (.fvar (g+1)) (.fvar (x+1)) (.fvar 0)) := by
    have h : ND.Proof C σ.free := assumption (by simp [C])
    convert h using 1 ; dsimp [σ]; traceSyntax
  have hi := pointAt (a+1) (b+1) (g+1) (x+1) 0 (up (pointShift a b g hp) σ.free)
  convert andLeft (mp hh (andLeft hi)) using 1 <;> (dsimp [C,σ] <;> traceSyntax)

def pointOutputBackward {Γ : List Form} (E : FormulaEquality Γ) (a b g x : Nat)
    (hp : ND.Proof Γ (pointGraph (.fvar a) (.fvar b) (.fvar g)))
    (hx : ND.Proof Γ (eq (.fvar x) (.fvar a))) :
    ND.Proof Γ (hasOutput (.fvar g) (.fvar x)) := by
  have hi := pointAt a b g x b hp
  have he := mp (andIntro hx (E.reflexive (.fvar b))) (andRight hi)
  apply exsIntro _ (.fvar b)
  convert he using 1 ; traceSyntax

def pointDomain {Γ : List Form} (E : FormulaEquality Γ) (a b g : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar a)))
    (hp : ND.Proof Γ (pointGraph (.fvar a) (.fvar b) (.fvar g))) :
    ND.Proof Γ (graphDomain (.fvar a) (.fvar g)) := by
  apply allIntro
  have pp := pointShift a b g hp
  have zz := Ordinal.zeroNotMem (a+1) 0 (Ordinal.zeroShift a hz)
  have result : ND.Proof (shifted Γ)
      (sourceIff (hasOutput (.fvar (g+1)) (.fvar 0))
        (mem (.fvar (a+1)) (.fvar 0) ⋎ eq (.fvar 0) (.fvar (a+1)))) := by
    apply andIntro
    · apply impIntro
      exact ND.orRight (pointOutputForward (a+1) (b+1) (g+1) 0 (up pp _) (assumption (by simp)))
    · apply impIntro
      let q : Form := mem (.fvar (a+1)) (.fvar 0) ⋎ eq (.fvar 0) (.fvar (a+1))
      have hd : ND.Proof (q::shifted Γ) q := assumption (by simp)
      apply orElim hd
      · exact botElim (contradiction (assumption (by simp)) (up (up zz q) _))
      · let EE : FormulaEquality (eq (.fvar 0) (.fvar (a+1)) :: q :: shifted Γ) :=
          E.shifted.weaken (fun r hr => List.mem_cons_of_mem _ (List.mem_cons_of_mem q hr))
        exact pointOutputBackward EE (a+1) (b+1) (g+1) 0 (up (up pp q) _) (assumption (by simp))
  convert result using 1 <;> (dsimp only [hasOutput] <;> traceSyntax)

#print axioms pointOutputForward
#print axioms pointOutputBackward
#print axioms pointDomain
end M6.PA.RelationalSource.PairGraph

