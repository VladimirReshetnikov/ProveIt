module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.InternalCodedSourceDrainTwo
public import M6.Source.AXTimes4
@[expose] public section
open M6.Arithmetic.PA
namespace M6.Arithmetic.PA.InternalTrace.CodedSource
open M6 M6.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

def times4EndGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “z n xs. ∃ a ys, !nthDef a xs 1 ∧ !(replaceGraph 7) ys xs 0 ∧
    !(replaceGraph 1) z ys (a+4*n)”
def times4Formula (base : Nat) : ArithmeticSemisentence 1 :=
  “n. ∀ xs, (!lenDef 9 xs ∧ !nthDef n xs 7) →
    ∃ ys a b cs, !times4EndGraph ys n xs ∧
      !adjoinDef a ↑(base+1) xs ∧ !adjoinDef b ↑(base+7) ys ∧
      !traceGraph (6*n+1) cs a b”
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
noncomputable def times4End (n xs : V) : V :=
  replace 1 (replace 7 xs 0) (registers xs 1+4*n)
theorem times4End_graph (z n xs : V) :
    times4EndGraph.val.Evalb ![z,n,xs] ↔ z=times4End n xs := by
  simp [times4EndGraph,(replace_defined 7).df,(replace_defined 1).df,
    times4End,registers,numeral_eq_natCast,Nat.cast_ofNat]
theorem times4_formula (base : Nat) (n : V) :
    (times4Formula base).Evalb ![n] ↔
      ∀ xs : V, ValidStore xs → registers xs 7=n → ∃ cs,
        Trace (6*n+1) cs (stateCode ((base+1:Nat):V) xs)
          (stateCode ((base+7:Nat):V) (times4End n xs)) := by
  simp [times4Formula,times4End_graph,trace_correct,ValidStore,registers,stateCode,
    numeral_eq_natCast,Nat.cast_ofNat,eq_comm,Matrix.comp_vecCons'']
#print axioms times4_formula
end M6.Arithmetic.PA.InternalTrace.CodedSource

