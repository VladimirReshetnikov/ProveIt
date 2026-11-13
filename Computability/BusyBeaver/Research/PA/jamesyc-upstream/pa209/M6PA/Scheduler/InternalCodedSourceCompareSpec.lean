module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.InternalCodedSourceCompareCleanup
@[expose] public section
open M6.Arithmetic.PA
namespace M6.Arithmetic.PA.InternalTrace.CodedSource
open M6 M6.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
def compareFormula (base same diff : Nat) : ArithmeticSemisentence 1 :=
  “h. ∀ xs x, !lenDef 9 xs → ∃ ys zs a b t cs,
    !guardStoreGraph ys xs h x ∧ !guardStoreGraph zs xs 0 0 ∧ !adjoinDef a ↑(base+1) ys ∧
    ((h=x ∧ !adjoinDef b ↑(same+1) zs) ∨ (h≠x ∧ !adjoinDef b ↑(diff+1) zs)) ∧
    0<t ∧ !traceGraph t cs a b”
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
lemma compare_formula (base same diff : Nat) (h : V) :
    (compareFormula base same diff).Evalb ![h] ↔ ∀xs x:V,ValidStore xs →∃t cs,0<t ∧
      Trace t cs (stateCode ((base+1:Nat):V) (guardStore xs h x))
        (stateCode (if h=x then ((same+1:Nat):V) else ((diff+1:Nat):V)) (guardStore xs 0 0)) := by
  simp only [compareFormula]
  -- All object quantifiers retain model-valued domains.
  simp [guardStore_graph,adjoin_defined.df,trace_correct,ValidStore,stateCode,
    len_defined.df,numeral_eq_natCast,Nat.cast_ofNat,eq_comm]
  constructor <;> intro H xs x hv <;> by_cases he : h=x <;> simpa [he] using H xs x hv
#print axioms compare_formula
end M6.Arithmetic.PA.InternalTrace.CodedSource

