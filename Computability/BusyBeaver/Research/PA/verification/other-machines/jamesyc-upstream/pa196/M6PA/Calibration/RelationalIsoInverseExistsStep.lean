module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoInverseSuccessorWitness
@[expose] public section

/-! Existential elimination supplies both the old prefix and the next value. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)

def inverseExistsStepAtValue {Γ : List Form} (E : FormulaEquality Γ) (g n s v : Nat)
    (hempty : ND.Proof Γ emptyFormula) (hadj : ND.Proof Γ adjunctionFormula)
    (hs : ND.Proof Γ (Ordinal.successor (.fvar n) (.fvar s)))
    (hv : ND.Proof Γ (edge (.fvar g) (.fvar n) (.fvar v)))
    (hi : ND.Proof Γ (inversePrefixExists (.fvar g) (.fvar n))) :
    ND.Proof Γ (inversePrefixExists (.fvar g) (.fvar s)) := by
  apply exsElim hi
  let σ : Formula 1 := inversePrefix (.fvar g) (.fvar n) (.bvar 0)
  let C := σ.free :: shifted Γ
  have hh : ND.Proof C (inversePrefix (.fvar (g+1)) (.fvar (n+1)) (.fvar 0)) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [σ] <;> inverseSyntax)
  have vv : ND.Proof (shifted Γ) (edge (.fvar (g+1)) (.fvar (n+1)) (.fvar (v+1))) := by
    convert shiftProof hv using 1 <;> inverseSyntax
  let I : InverseFrame C (g+1) (n+1) (s+1) 0 (v+1) := {
    equality := E.shifted.weaken (fun p hp => List.mem_cons_of_mem σ.free hp)
    empty := up (emptyClosedShift hempty) σ.free
    adjunction := up (adjunctionClosedShift hadj) σ.free
    graph := hh
    successor := up (Ordinal.successorShift n s hs) σ.free
    forward := up vv σ.free }
  have out := inverseStepWitness (g+1) (n+1) (s+1) 0 (v+1) I
  convert out using 1 <;> (dsimp [C,σ] <;> inverseSyntax)

def inverseExistsStep {Γ : List Form} (E : FormulaEquality Γ) (g n s : Nat)
    (hempty : ND.Proof Γ emptyFormula) (hadj : ND.Proof Γ adjunctionFormula)
    (hs : ND.Proof Γ (Ordinal.successor (.fvar n) (.fvar s)))
    (hv : ND.Proof Γ (∃¹ edge (.fvar g) (.fvar n) (.bvar 0)))
    (hi : ND.Proof Γ (inversePrefixExists (.fvar g) (.fvar n))) :
    ND.Proof Γ (inversePrefixExists (.fvar g) (.fvar s)) := by
  apply exsElim hv
  let σ : Formula 1 := edge (.fvar g) (.fvar n) (.bvar 0)
  let C := σ.free :: shifted Γ
  have hh : ND.Proof C (edge (.fvar (g+1)) (.fvar (n+1)) (.fvar 0)) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [σ] <;> inverseSyntax)
  have ii : ND.Proof (shifted Γ) (inversePrefixExists (.fvar (g+1)) (.fvar (n+1))) := by
    convert shiftProof hi using 1 <;> inverseSyntax
  have out := inverseExistsStepAtValue (E.shifted.weaken (fun p hp => List.mem_cons_of_mem σ.free hp))
    (g+1) (n+1) (s+1) 0 (up (emptyClosedShift hempty) σ.free)
    (up (adjunctionClosedShift hadj) σ.free) (up (Ordinal.successorShift n s hs) σ.free)
    hh (up ii σ.free)
  convert out using 1 <;> (dsimp [C,σ] <;> inverseSyntax)

#print axioms inverseExistsStepAtValue
#print axioms inverseExistsStep
end M6.PA.RelationalSource.PairGraph
