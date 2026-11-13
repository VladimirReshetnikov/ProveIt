module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoCompositionExists
public import M6PA.Calibration.RelationalParameterFresh
public import M6PA.Calibration.RelationalIsoCompositionTransitivitySyntax
@[expose] public section

/-! Existential transitivity with both graph parameters explicitly closed in
the exact Separation axiom and opened at their actual eigenvariables. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)

def compositionHalfSeparation (g a : Nat) : Form :=
  closeParameter (separationFormula (∼compositionProperty (g+1) 0 (a+1)))
def compositionClosedSeparation (a : Nat) : Form :=
  closeParameter (compositionHalfSeparation 0 (a+1))

set_option maxHeartbeats 800000 in
def compositionIsoFromLeftGraph {Γ : List Form} (E : FormulaEquality Γ) (g a b c : Nat)
    (hempty : ND.Proof Γ emptyFormula) (hadj : ND.Proof Γ adjunctionFormula)
    (hi : ND.Proof Γ Ordinal.intersectionFormula)
    (hsep : ND.Proof Γ (compositionHalfSeparation g a))
    (hg : ND.Proof Γ (orderBijection (.fvar g) (.fvar a) (.fvar b)))
    (hh : ND.Proof Γ (orderIso (.fvar b) (.fvar c)))
    (hd : ND.Proof Γ (Ordinal.domain (.fvar a))) :
    ND.Proof Γ (orderIso (.fvar a) (.fvar c)) := by
  apply exsElim hh
  let σ : Formula 1 := orderBijection (.bvar 0) (.fvar b) (.fvar c)
  let C := σ.free :: shifted Γ
  have hh' : ND.Proof C (orderBijection (.fvar 0) (.fvar (b+1)) (.fvar (c+1))) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    simpa only [σ,compositionBijectionFreeEq] using hh
  have gg : ND.Proof C (orderBijection (.fvar (g+1)) (.fvar (a+1)) (.fvar (b+1))) := by
    simpa only [compositionBijectionShiftEq] using up (shiftProof hg) σ.free
  have ss : ND.Proof (shifted Γ) (separationFormula (∼compositionProperty (g+1) 0 (a+1))) :=
    freshParameter _ hsep
  have out := compositionIsoOfBijections (E.shifted.weaken (fun p hp => List.mem_cons_of_mem σ.free hp))
    (g+1) 0 (a+1) (b+1) (c+1) (up (emptyClosedShift hempty) σ.free)
    (up (adjunctionClosedShift hadj) σ.free) (up (Ordinal.intersectionAxiomShift hi) σ.free)
    (up ss σ.free) gg hh' (up (Ordinal.domainShift a hd) σ.free)
  simpa only [C,σ,Rew.bShift_fvar,compositionIsoShiftEq] using out

set_option maxHeartbeats 800000 in
def compositionIsoTransitivity {Γ : List Form} (E : FormulaEquality Γ) (a b c : Nat)
    (hempty : ND.Proof Γ emptyFormula) (hadj : ND.Proof Γ adjunctionFormula)
    (hi : ND.Proof Γ Ordinal.intersectionFormula)
    (hsep : ND.Proof Γ (compositionClosedSeparation a))
    (hg : ND.Proof Γ (orderIso (.fvar a) (.fvar b)))
    (hh : ND.Proof Γ (orderIso (.fvar b) (.fvar c)))
    (hd : ND.Proof Γ (Ordinal.domain (.fvar a))) :
    ND.Proof Γ (orderIso (.fvar a) (.fvar c)) := by
  apply exsElim hg
  let σ : Formula 1 := orderBijection (.bvar 0) (.fvar a) (.fvar b)
  let C := σ.free :: shifted Γ
  have gg : ND.Proof C (orderBijection (.fvar 0) (.fvar (a+1)) (.fvar (b+1))) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    simpa only [σ,compositionBijectionFreeEq] using hh
  have hh' : ND.Proof C (orderIso (.fvar (b+1)) (.fvar (c+1))) := by
    simpa only [compositionIsoShiftEq] using up (shiftProof hh) σ.free
  have ss : ND.Proof (shifted Γ) (compositionHalfSeparation 0 (a+1)) := freshParameter _ hsep
  have out := compositionIsoFromLeftGraph (E.shifted.weaken (fun p hp => List.mem_cons_of_mem σ.free hp))
    0 (a+1) (b+1) (c+1) (up (emptyClosedShift hempty) σ.free)
    (up (adjunctionClosedShift hadj) σ.free) (up (Ordinal.intersectionAxiomShift hi) σ.free)
    (up ss σ.free) gg hh' (up (Ordinal.domainShift a hd) σ.free)
  simpa only [C,σ,Rew.bShift_fvar,compositionIsoShiftEq] using out

#print axioms compositionIsoFromLeftGraph
#print axioms compositionIsoTransitivity
end M6.PA.RelationalSource.PairGraph
