module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoZeroTransport
@[expose] public section

/-! The interpreted zero predicate respects the exact existential order
isomorphism, without identifying the two underlying set objects. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)

def orderIsoZeroForward {Γ : List Form} (a b : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar a)))
    (hi : ND.Proof Γ (orderIso (.fvar a) (.fvar b))) :
    ND.Proof Γ (Ordinal.zero (.fvar b)) := by
  apply exsElim hi
  let σ : Formula 1 := orderBijection (.bvar 0) (.fvar a) (.fvar b)
  let C := σ.free :: shifted Γ
  have hg : ND.Proof C (orderBijection (.fvar 0) (.fvar (a+1)) (.fvar (b+1))) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [σ] <;> isoSyntax)
  have out := zeroByRightTotal 0 (a+1) (b+1) (up (Ordinal.zeroShift a hz) σ.free)
    (andLeft (andRight hg)) (andLeft (andRight (andRight (andRight hg))))
  convert out using 1 <;> (dsimp [C,σ] <;> isoSyntax)

def orderIsoZeroBackward {Γ : List Form} (a b : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar b)))
    (hi : ND.Proof Γ (orderIso (.fvar a) (.fvar b))) :
    ND.Proof Γ (Ordinal.zero (.fvar a)) := by
  apply exsElim hi
  let σ : Formula 1 := orderBijection (.bvar 0) (.fvar a) (.fvar b)
  let C := σ.free :: shifted Γ
  have hg : ND.Proof C (orderBijection (.fvar 0) (.fvar (a+1)) (.fvar (b+1))) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [σ] <;> isoSyntax)
  have out := zeroByLeftTotal 0 (a+1) (b+1) (up (Ordinal.zeroShift b hz) σ.free)
    (andLeft (andRight hg)) (andLeft (andRight (andRight hg)))
  convert out using 1 <;> (dsimp [C,σ] <;> isoSyntax)

def orderIsoZeroIff {Γ : List Form} (a b : Nat)
    (hi : ND.Proof Γ (orderIso (.fvar a) (.fvar b))) :
    ND.Proof Γ (sourceIff (Ordinal.zero (.fvar a)) (Ordinal.zero (.fvar b))) := by
  apply andIntro
  · apply impIntro
    let d : Form := Ordinal.zero (.fvar a)
    exact orderIsoZeroForward a b (assumption (by simp [d])) (up hi d)
  · apply impIntro
    let d : Form := Ordinal.zero (.fvar b)
    exact orderIsoZeroBackward a b (assumption (by simp [d])) (up hi d)

#print axioms orderIsoZeroForward
#print axioms orderIsoZeroBackward
#print axioms orderIsoZeroIff
end M6.PA.RelationalSource.PairGraph
