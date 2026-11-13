module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoCompositionSuccessorWitness
@[expose] public section

/-! Supply the old graph and actual intermediate/output coordinate witnesses
by finite existential elimination. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)

def compositionExistsStepAtValues {Γ : List Form} (E : FormulaEquality Γ) (g h n s y z : Nat)
    (hempty : ND.Proof Γ emptyFormula) (hadj : ND.Proof Γ adjunctionFormula)
    (hs : ND.Proof Γ (Ordinal.successor (.fvar n) (.fvar s)))
    (hg : ND.Proof Γ (edge (.fvar g) (.fvar n) (.fvar y)))
    (hh : ND.Proof Γ (edge (.fvar h) (.fvar y) (.fvar z)))
    (hi : ND.Proof Γ (compositionPrefixExists (.fvar g) (.fvar h) (.fvar n))) :
    ND.Proof Γ (compositionPrefixExists (.fvar g) (.fvar h) (.fvar s)) := by
  apply exsElim hi
  let σ : Formula 1 := compositionPrefix (.fvar g) (.fvar h) (.fvar n) (.bvar 0)
  let C := σ.free :: shifted Γ
  have hk : ND.Proof C (compositionPrefix (.fvar (g+1)) (.fvar (h+1)) (.fvar (n+1)) (.fvar 0)) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [σ] <;> compositionSyntax)
  have gg : ND.Proof C (edge (.fvar (g+1)) (.fvar (n+1)) (.fvar (y+1))) := by
    convert up (shiftProof hg) σ.free using 1 <;> compositionSyntax
  have hh' : ND.Proof C (edge (.fvar (h+1)) (.fvar (y+1)) (.fvar (z+1))) := by
    convert up (shiftProof hh) σ.free using 1 <;> compositionSyntax
  let I : CompositionFrame C (g+1) (h+1) (n+1) (s+1) 0 (y+1) (z+1) := {
    equality := E.shifted.weaken (fun p hp => List.mem_cons_of_mem σ.free hp)
    empty := up (emptyClosedShift hempty) σ.free
    adjunction := up (adjunctionClosedShift hadj) σ.free
    graph := hk
    successor := up (Ordinal.successorShift n s hs) σ.free
    leftEdge := gg
    rightEdge := hh' }
  have out := compositionStepWitness (g+1) (h+1) (n+1) (s+1) 0 (y+1) (z+1) I
  convert out using 1 <;> (dsimp [C,σ] <;> compositionSyntax)

def compositionExistsStepAtEdge {Γ : List Form} (E : FormulaEquality Γ) (g h n s z : Nat)
    (hempty : ND.Proof Γ emptyFormula) (hadj : ND.Proof Γ adjunctionFormula)
    (hs : ND.Proof Γ (Ordinal.successor (.fvar n) (.fvar s)))
    (he : ND.Proof Γ (compositionEdge (.fvar g) (.fvar h) (.fvar n) (.fvar z)))
    (hi : ND.Proof Γ (compositionPrefixExists (.fvar g) (.fvar h) (.fvar n))) :
    ND.Proof Γ (compositionPrefixExists (.fvar g) (.fvar h) (.fvar s)) := by
  apply compositionEdgeEliminate g h n z _ he
  intro Δ inc hg hh
  have ii : ND.Proof Δ (compositionPrefixExists (.fvar (g+1)) (.fvar (h+1)) (.fvar (n+1))) := by
    convert ND.weaken (shiftProof hi) inc using 1 <;> compositionSyntax
  have out := compositionExistsStepAtValues (E.shifted.weaken inc) (g+1) (h+1) (n+1) (s+1) 0 (z+1)
    (ND.weaken (emptyClosedShift hempty) inc) (ND.weaken (adjunctionClosedShift hadj) inc)
    (ND.weaken (Ordinal.successorShift n s hs) inc) hg hh ii
  convert out using 1 <;> compositionSyntax

def compositionExistsStep {Γ : List Form} (E : FormulaEquality Γ) (g h n s : Nat)
    (hempty : ND.Proof Γ emptyFormula) (hadj : ND.Proof Γ adjunctionFormula)
    (hs : ND.Proof Γ (Ordinal.successor (.fvar n) (.fvar s)))
    (he : ND.Proof Γ (∃¹ compositionEdge (.fvar g) (.fvar h) (.fvar n) (.bvar 0)))
    (hi : ND.Proof Γ (compositionPrefixExists (.fvar g) (.fvar h) (.fvar n))) :
    ND.Proof Γ (compositionPrefixExists (.fvar g) (.fvar h) (.fvar s)) := by
  apply exsElim he
  let σ : Formula 1 := compositionEdge (.fvar g) (.fvar h) (.fvar n) (.bvar 0)
  let C := σ.free :: shifted Γ
  have hh : ND.Proof C (compositionEdge (.fvar (g+1)) (.fvar (h+1)) (.fvar (n+1)) (.fvar 0)) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [σ] <;> compositionSyntax)
  have ii : ND.Proof C (compositionPrefixExists (.fvar (g+1)) (.fvar (h+1)) (.fvar (n+1))) := by
    convert up (shiftProof hi) σ.free using 1 <;> compositionSyntax
  have out := compositionExistsStepAtEdge (E.shifted.weaken (fun p hp => List.mem_cons_of_mem σ.free hp))
    (g+1) (h+1) (n+1) (s+1) 0 (up (emptyClosedShift hempty) σ.free)
    (up (adjunctionClosedShift hadj) σ.free) (up (Ordinal.successorShift n s hs) σ.free) hh ii
  convert out using 1 <;> (dsimp [C,σ] <;> compositionSyntax)

#print axioms compositionExistsStepAtValues
#print axioms compositionExistsStepAtEdge
#print axioms compositionExistsStep
end M6.PA.RelationalSource.PairGraph
