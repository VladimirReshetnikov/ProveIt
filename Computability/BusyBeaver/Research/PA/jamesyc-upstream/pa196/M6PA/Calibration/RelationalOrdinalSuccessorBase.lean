module
public import M6PA.Theory
public import M6PA.Calibration.RelationalOrdinalEmpty
public import M6PA.Calibration.RelationalSourceAdjunction
@[expose] public section

/-! Raw successor existence is a finite specialization of the already proved
nonextensional adjunction axiom. This does not assert closure of the ordinal
domain under successors; that needs a separate finite argument. -/
namespace M6.PA.RelationalSource.Ordinal
open FFL FFL.FirstOrder ND

def successorExists (a : Term n) : Formula n :=
  ∃¹ successor (Rew.bShift a) (.bvar 0)

/-- Specialize the two adjunction inputs to the same object. -/
def rawSuccessor {Γ : List Form} (a : Term 0)
    (d : ND.Proof Γ adjunctionFormula) : ND.Proof Γ (successorExists a) := by
  cases a with
  | bvar i => nomatch i
  | func f _ => nomatch f
  | fvar i =>
    have first := allElim _ (.fvar i) d
    have second := allElim _ (.fvar i) first
    convert second using 1 ;
      simp only [successorExists,successor,memAtom,eqAtom,
        mem,eq,sourceIff,sourceImply,Rewriting.subst,app_eq_rewAux,
        Semiformula.rewAux,Semiformula.neg] ;
      finishSourceSyntax

def rawSuccessorDerivation (a : Term 0) :
    ND.Proof [adjunctionFormula] (successorExists a) :=
  rawSuccessor a (assumption (by simp))

/-- Actual finite numeric proof, with all allocator and proof budgets exposed. -/
def rawSuccessorSupplier (a : Term 0) (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i, f i < lo) (hz : lo+6 < z)
    (hadj : lo+2+lkBudget adjunctionDerivation ≤ z)
    (hbudget : lo+lkBudget (rawSuccessorDerivation a) ≤ z) :
    NativeCalculus.ActualBasis.Proof (code (successorExists a) f lo z) := by
  apply compileContext [adjunctionFormula] (successorExists a)
    (rawSuccessorDerivation a) f lo z hlo hf hbudget
  intro p hp
  have he : p = adjunctionFormula := by simpa using hp
  subst p
  exact adjunctionSupplier f lo z hlo hz hadj

#print axioms rawSuccessor
#print axioms rawSuccessorSupplier
end M6.PA.RelationalSource.Ordinal
