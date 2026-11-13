module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoInverseExists
public import M6PA.Calibration.RelationalParameterFresh
@[expose] public section

/-! Existential symmetry using an explicitly closed Separation instance.
The graph eigenvariable is opened by the reusable fresh-parameter rule. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)

def inverseClosedSeparation (a : Nat) : Form :=
  closeParameter (separationFormula (∼inverseProperty 0 (a+1)))

set_option maxHeartbeats 800000 in
def inverseIsoSymmetry {Γ : List Form} (E : FormulaEquality Γ) (a b : Nat)
    (hempty : ND.Proof Γ emptyFormula) (hadj : ND.Proof Γ adjunctionFormula)
    (hi : ND.Proof Γ Ordinal.intersectionFormula)
    (hsep : ND.Proof Γ (inverseClosedSeparation a))
    (hg : ND.Proof Γ (orderIso (.fvar a) (.fvar b)))
    (hd : ND.Proof Γ (Ordinal.domain (.fvar a))) :
    ND.Proof Γ (orderIso (.fvar b) (.fvar a)) := by
  apply exsElim hg
  let σ : Formula 1 := orderBijection (.bvar 0) (.fvar a) (.fvar b)
  let C := σ.free :: shifted Γ
  have hh : ND.Proof C (orderBijection (.fvar 0) (.fvar (a+1)) (.fvar (b+1))) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [σ] <;> inverseSyntax)
  have ss : ND.Proof (shifted Γ) (separationFormula (∼inverseProperty 0 (a+1))) :=
    freshParameter _ hsep
  have out := inverseIsoOfBijection (E.shifted.weaken (fun p hp => List.mem_cons_of_mem σ.free hp))
    0 (a+1) (b+1) (up (emptyClosedShift hempty) σ.free) (up (adjunctionClosedShift hadj) σ.free)
    (up (Ordinal.intersectionAxiomShift hi) σ.free) (up ss σ.free) hh (up (Ordinal.domainShift a hd) σ.free)
  convert out using 1 <;> (dsimp [C,σ] <;> inverseSyntax)

#print axioms inverseIsoSymmetry
end M6.PA.RelationalSource.PairGraph
