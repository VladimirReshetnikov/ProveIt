module
public import PA196.Arithmetic.Scheduler.Base
public import PA196.Program
public import PA196.Source.Readers
public import PA196.Arithmetic.Machine.PATheory
public import PA196.Arithmetic.Scheduler.InternalCodedSourceS36Drain
@[expose] public section
open PA196.Arithmetic.Machine.PA
namespace PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource
open M6 M6.PA PA196.Arithmetic PA196.Arithmetic.Scheduler
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

def drainTwoEndGraph (r s u : Fin 9) : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “z n xs. ∃ a ys, !nthDef a xs ↑u.val ∧ !(drainEndGraph r s) ys n xs ∧
    !(replaceGraph u.val) z ys (a+n)”
def drainTwoFormula (entry exit : Nat) (r s u : Fin 9) : ArithmeticSemisentence 1 :=
  “n. ∀ xs, (!lenDef 9 xs ∧ !nthDef n xs ↑r.val) →
    ∃ ys a b cs, !(drainTwoEndGraph r s u) ys n xs ∧
      !adjoinDef a ↑(entry+1) xs ∧ !adjoinDef b ↑(exit+1) ys ∧
      !traceGraph (4*n+1) cs a b”
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* PA196.Arithmetic.Machine.PA.theory]
noncomputable def drainTwoEnd (r s u : Fin 9) (n xs : V) : V :=
  replace u.val (drainEnd r s n xs) (registers xs u+n)
theorem drainTwoEnd_graph (r s u : Fin 9) (z n xs : V) :
    (drainTwoEndGraph r s u).val.Evalb ![z,n,xs] ↔ z=drainTwoEnd r s u n xs := by
  simp [drainTwoEndGraph,drainEnd_graph,(replace_defined u.val).df,
    drainTwoEnd,registers,numeral_eq_natCast]
theorem drainTwo_formula (entry exit : Nat) (r s u : Fin 9) (n : V) :
    (drainTwoFormula entry exit r s u).Evalb ![n] ↔
      ∀ xs : V, ValidStore xs → registers xs r=n → ∃ cs,
        Trace (4*n+1) cs (stateCode ((entry+1:Nat):V) xs)
          (stateCode ((exit+1:Nat):V) (drainTwoEnd r s u n xs)) := by
  simp [drainTwoFormula,drainTwoEnd_graph,trace_correct,ValidStore,registers,stateCode,
    numeral_eq_natCast,eq_comm,Matrix.comp_vecCons'']
#print axioms drainTwo_formula
end PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource

