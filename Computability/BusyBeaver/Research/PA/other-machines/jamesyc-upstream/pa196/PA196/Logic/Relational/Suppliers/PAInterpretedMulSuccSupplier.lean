module
public import M6PA.Calibration.PAInterpretedMulSuccSupplier
public import PA196.Logic.Relational.SourceAdjunction
public import PA196.Logic.Relational.SourceCode
public import PA196.Logic.Relational.SourceContext
public import PA196.Logic.Relational.SourceIntersection
public import PA196.Logic.Relational.Suppliers.PAInterpretedAddSuccSupplier
public import PA196.Logic.Relational.Suppliers.RelationalAdditionCommutativitySupplier
public import PA196.Logic.Relational.Suppliers.RelationalOrderIsoClosedTransitivity
@[expose] public section

/-! New PA196 certificates for the original finite source proof templates.
Only native supplier outputs are retargeted; source formulas, Foundation LK
derivations and numeric resource bounds are imported unchanged. -/
noncomputable section

namespace PA196.Logic.Relational.ForwardRelational
open FFL FFL.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND
open M6.PA.ForwardRelational
open PA196.Logic PA196.Logic.Relational
open M6.PA.NativeCalculus (renameLabel)
open FFL FFL.FirstOrder M6.PA.RelationalSource ND
open M6.PA.RelationalSource.Ordinal (Term Formula)
open M6.PA.RelationalSource.PairGraph

def interpretedMulSuccAxiomSupplier (f : Nat → Nat) (lo z : Nat)
    (B : FunctionCongruenceBudgets f lo z) (C : AdditionCommutativityBudget f lo z)
    (hcomm : lo+lkBudget addCommutativityDerivation≤z)
    (hsymSep : lo+6+depth (∼inverseProperty 0 (1+1))≤z)
    (hsymProof : lo+2+lkBudget (inverseSymmetryDerivation 1 0)≤z)
    (p : Form) (hp : p∈interpretedMulSuccAxioms) : PA196.Logic.Derivation (PA196.Logic.Relational.Source.code p f lo z) := by
  classical
  by_cases h0 : p=addCommutativityStatement
  · subst p; exact PA196.Logic.Relational.Source.PairGraph.addCommutativitySupplier f lo z C hcomm
  by_cases h1 : p=isoTransitivityClosed
  · subst p; exact PA196.Logic.Relational.Source.PairGraph.isoTransitivityClosedSupplier f lo z C.positive C.labels C.margin
      C.transitivitySeparation C.adjunction C.transitivityProof
  have h : p∈interpretedAddSuccAxioms := by simpa [interpretedMulSuccAxioms,h0,h1] using hp
  have hz := C.margin
  have ha := C.adjunction
  exact PA196.Logic.Relational.ForwardRelational.interpretedAddSuccAxiomSupplier f lo z B (by omega) C.identitySeparation C.identityProof
    hsymSep (by omega) hsymProof p h
#print axioms interpretedMulSuccAxiomSupplier
end PA196.Logic.Relational.ForwardRelational

namespace PA196.Logic.Relational.ForwardRelational
open FFL FFL.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND
open M6.PA.ForwardRelational
open PA196.Logic PA196.Logic.Relational
open M6.PA.NativeCalculus (renameLabel)
open FFL FFL.FirstOrder M6.PA.RelationalSource ND
open M6.PA.RelationalSource.Ordinal (Term Formula)
open M6.PA.RelationalSource.PairGraph

def interpretedMulSuccSupplier (ρ : Nat → Term 0) (f : Nat → Nat) (lo z : Nat)
    (B : FunctionCongruenceBudgets f lo z) (C : AdditionCommutativityBudget f lo z)
    (hcomm : lo+lkBudget addCommutativityDerivation≤z)
    (hsymSep : lo+6+depth (∼inverseProperty 0 (1+1))≤z)
    (hsymProof : lo+2+lkBudget (inverseSymmetryDerivation 1 0)≤z)
    (hbudget : lo+lkBudget (interpretedMulSuccDerivation ρ)≤z) :
    PA196.Logic.Derivation (PA196.Logic.Relational.Source.code (formula M6.PA.Presentation.mulSucc Fin.elim0 ρ) f lo z) :=
  PA196.Logic.Relational.Source.compileContext interpretedMulSuccAxioms _ (interpretedMulSuccDerivation ρ) f lo z
    B.positive B.labels hbudget (PA196.Logic.Relational.ForwardRelational.interpretedMulSuccAxiomSupplier f lo z B C hcomm hsymSep hsymProof)
#print axioms interpretedMulSuccSupplier
end PA196.Logic.Relational.ForwardRelational
end
