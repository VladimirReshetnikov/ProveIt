module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedInductionSupplier
public import M6PA.Calibration.PAInterpretedParameterClosure
@[expose] public section

/-! Close the already fully supplied finite guarded induction theorem.
The result is an actual plain target universal closure. Equivalence with the
literal guarded source univCl' remains a separate syntactic proof obligation. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)

def inductionClosureCount (p : SourceFormula 1) : Nat :=
  (Presentation.inductionFormula p).fvSup

theorem inductionGuardIndex_bound (p : SourceFormula 1) (i : Nat)
    (hi : i ∈ p.freeVariables.sort (· ≤ ·)) : i < inductionClosureCount p := by
  apply Semiformula.lt_fvSup_of_fvar?
  have hm : i ∈ p.freeVariables := (Finset.mem_sort (· ≤ ·)).mp hi
  exact Finset.mem_union_right _ (Finset.mem_union_right _ hm)

def inductionClosedGuard (p : SourceFormula 1) : Form :=
  closeParameters (inductionClosureCount p) (interpretedInductionGuarded p Semiterm.fvar)

def inductionClosedGuardSupplier (p : SourceFormula 1) (f : Nat → Nat) (lo z : Nat)
    (B : InterpretedInductionBudget p Semiterm.fvar
      (closureLabels (inductionClosureCount p) f lo) (lo+inductionClosureCount p) z)
    (hbudget : lo+inductionClosureCount p+
      lkBudget (interpretedInductionDerivation p Semiterm.fvar) ≤ z) :
    NativeCalculus.ActualBasis.Proof (code (inductionClosedGuard p) f lo z) := by
  apply closeParametersSupplier
  exact interpretedInductionSupplier p Semiterm.fvar _ _ z B hbudget

#print axioms inductionGuardIndex_bound
#print axioms inductionClosedGuardSupplier
end M6.PA.ForwardRelational

