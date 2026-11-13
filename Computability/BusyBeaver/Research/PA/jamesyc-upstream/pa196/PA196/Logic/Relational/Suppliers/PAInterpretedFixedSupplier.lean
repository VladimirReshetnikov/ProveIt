module
public import M6PA.Calibration.PAInterpretedFixedSupplier
public import PA196.Logic.Relational.SourceAdjunction
public import PA196.Logic.Relational.SourceCode
public import PA196.Logic.Relational.SourceContext
public import PA196.Logic.Relational.SourceIntersection
public import PA196.Logic.Relational.Suppliers.PAInterpretedMulSuccSupplier
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

def interpretedFixedAxiomSupplier (f : Nat → Nat) (lo z : Nat)
    (B : FunctionCongruenceBudgets f lo z) (C : AdditionCommutativityBudget f lo z)
    (hcomm : lo+lkBudget addCommutativityDerivation≤z)
    (hsymSep : lo+6+depth (∼inverseProperty 0 (1+1))≤z)
    (hsymProof : lo+2+lkBudget (inverseSymmetryDerivation 1 0)≤z)
    (q : Form) (hq : q∈interpretedFixedAxioms) : PA196.Logic.Derivation (PA196.Logic.Relational.Source.code q f lo z) := by
  classical
  by_cases he : q=closedStrictSeparation
  · subst q
    exact PA196.Logic.Relational.Source.closedSeparationSupplier _ f lo z B.positive B.labels B.strictEntry
  exact PA196.Logic.Relational.ForwardRelational.interpretedMulSuccAxiomSupplier f lo z B C hcomm hsymSep hsymProof q
    ((List.mem_cons.mp hq).resolve_left he)
#print axioms interpretedFixedAxiomSupplier
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

def interpretedFixedSupplier (p : SourceFormula 0) (hp : p∈M6.PA.Presentation.fixedAxioms)
    (ρ : Nat → Term 0) (f : Nat → Nat) (lo z : Nat)
    (B : FunctionCongruenceBudgets f lo z) (C : AdditionCommutativityBudget f lo z)
    (hcomm : lo+lkBudget addCommutativityDerivation≤z)
    (hsymSep : lo+6+depth (∼inverseProperty 0 (1+1))≤z)
    (hsymProof : lo+2+lkBudget (inverseSymmetryDerivation 1 0)≤z)
    (hbudget : lo+lkBudget (interpretedFixedDerivation p hp ρ)≤z) :
    PA196.Logic.Derivation (PA196.Logic.Relational.Source.code (formula p Fin.elim0 ρ) f lo z) :=
  PA196.Logic.Relational.Source.compileContext interpretedFixedAxioms _ (interpretedFixedDerivation p hp ρ) f lo z
    B.positive B.labels hbudget (PA196.Logic.Relational.ForwardRelational.interpretedFixedAxiomSupplier f lo z B C hcomm hsymSep hsymProof)
#print axioms interpretedFixedSupplier
end PA196.Logic.Relational.ForwardRelational
end
