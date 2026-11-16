module
public import M6PA.Calibration.PAInterpretedAddSuccSupplier
public import PA196.Logic.Relational.SourceAdjunction
public import PA196.Logic.Relational.SourceCode
public import PA196.Logic.Relational.SourceContext
public import PA196.Logic.Relational.SourceIntersection
public import PA196.Logic.Relational.Suppliers.PAInterpretedFunctionCongruenceContext
public import PA196.Logic.Relational.Suppliers.RelationalIdentitySupplier
public import PA196.Logic.Relational.Suppliers.RelationalOrderIsoClosedSymmetry
public import PA196.Logic.Relational.Suppliers.RelationalParameterClosure
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

def interpretedAddSuccAxiomSupplier (f : Nat → Nat) (lo z : Nat)
    (B : FunctionCongruenceBudgets f lo z) (hz : lo+8<z)
    (hidentitySep : lo+3+depth (∼identityProperty)≤z)
    (hidentityProof : lo+lkBudget identityDerivation≤z)
    (hsymSep : lo+6+depth (∼inverseProperty 0 (1+1))≤z)
    (hadj : lo+4+lkBudget adjunctionDerivation≤z)
    (hsymProof : lo+2+lkBudget (inverseSymmetryDerivation 1 0)≤z)
    (p : Form) (hp : p∈interpretedAddSuccAxioms) : PA196.Logic.Derivation (PA196.Logic.Relational.Source.code p f lo z) := by
  classical
  by_cases h0 : p=identityStatement
  · subst p; exact PA196.Logic.Relational.Source.PairGraph.identitySupplier f lo z B.positive B.labels (by omega) hidentitySep (by omega) hidentityProof
  by_cases h1 : p=closedInclusiveSeparation
  · subst p; exact PA196.Logic.Relational.Source.closedSeparationSupplier _ f lo z B.positive B.labels B.domainEntry
  by_cases h2 : p=isoSymmetryClosed
  · subst p; exact PA196.Logic.Relational.Source.PairGraph.isoSymmetryClosedSupplier f lo z B.positive B.labels hz hsymSep hadj hsymProof
  have h : p∈functionCongruenceAxioms := by simpa [interpretedAddSuccAxioms,h0,h1,h2] using hp
  exact PA196.Logic.Relational.ForwardRelational.functionCongruenceAxiomSupplier f lo z B p h
#print axioms interpretedAddSuccAxiomSupplier
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

def interpretedAddSuccSupplier (ρ : Nat → Term 0) (f : Nat → Nat) (lo z : Nat)
    (B : FunctionCongruenceBudgets f lo z) (hz : lo+8<z)
    (hidentitySep : lo+3+depth (∼identityProperty)≤z)
    (hidentityProof : lo+lkBudget identityDerivation≤z)
    (hsymSep : lo+6+depth (∼inverseProperty 0 (1+1))≤z)
    (hadj : lo+4+lkBudget adjunctionDerivation≤z)
    (hsymProof : lo+2+lkBudget (inverseSymmetryDerivation 1 0)≤z)
    (hbudget : lo+lkBudget (interpretedAddSuccDerivation ρ)≤z) :
    PA196.Logic.Derivation (PA196.Logic.Relational.Source.code (formula M6.PA.Presentation.addSucc Fin.elim0 ρ) f lo z) :=
  PA196.Logic.Relational.Source.compileContext interpretedAddSuccAxioms _ (interpretedAddSuccDerivation ρ) f lo z
    B.positive B.labels hbudget
    (PA196.Logic.Relational.ForwardRelational.interpretedAddSuccAxiomSupplier f lo z B hz hidentitySep hidentityProof hsymSep hadj hsymProof)
#print axioms interpretedAddSuccSupplier
end PA196.Logic.Relational.ForwardRelational
end
