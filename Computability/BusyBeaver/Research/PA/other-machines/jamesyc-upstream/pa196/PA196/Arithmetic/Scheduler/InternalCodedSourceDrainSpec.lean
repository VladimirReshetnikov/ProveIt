module
public import PA196.Arithmetic.Scheduler.Base
public import PA196.Program
public import PA196.Source.Readers
public import PA196.Arithmetic.Machine.PATheory
public import PA196.Arithmetic.Scheduler.InternalCodedSourceLoopRegisters
@[expose] public section
open PA196.Arithmetic.Machine.PA
namespace PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource
open M6 M6.PA PA196.Arithmetic PA196.Arithmetic.Scheduler
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

def drainEndGraph (r s : Fin 9) : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “z n xs. ∃ a ys, !nthDef a xs ↑s.val ∧ !(replaceGraph r.val) ys xs 0 ∧
    !(replaceGraph s.val) z ys (a+n)”
def drainFormula (entry exit : Nat) (r s : Fin 9) : ArithmeticSemisentence 1 :=
  “n. ∀ xs, (!lenDef 9 xs ∧ !nthDef n xs ↑r.val) →
    ∃ ys a b cs, !(drainEndGraph r s) ys n xs ∧
      !adjoinDef a ↑(entry+1) xs ∧ !adjoinDef b ↑(exit+1) ys ∧
      !traceGraph (3*n+1) cs a b”
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* PA196.Arithmetic.Machine.PA.theory]
noncomputable def drainEnd (r s : Fin 9) (n xs : V) : V :=
  replace s.val (replace r.val xs 0) (registers xs s+n)
theorem drainEnd_graph (r s : Fin 9) (z n xs : V) :
    (drainEndGraph r s).val.Evalb ![z,n,xs] ↔ z=drainEnd r s n xs := by
  simp [drainEndGraph,(replace_defined r.val).df,(replace_defined s.val).df,
    drainEnd,registers,numeral_eq_natCast]
theorem drain_formula (entry exit : Nat) (r s : Fin 9) (n : V) :
    (drainFormula entry exit r s).Evalb ![n] ↔
      ∀ xs : V, ValidStore xs → registers xs r=n → ∃ cs,
        Trace (3*n+1) cs (stateCode ((entry+1:Nat):V) xs)
          (stateCode ((exit+1:Nat):V) (drainEnd r s n xs)) := by
  simp [drainFormula,drainEnd_graph,trace_correct,ValidStore,registers,stateCode,
    numeral_eq_natCast,eq_comm,Matrix.comp_vecCons'']

theorem literal_step (i : Nat) (hi : i<3812) (inst : Source.Instruction)
    (hb : Source.resolveAt PA196.Program.sites i=some inst) (xs : V) :
    stepValue (stateCode ((i+1:Nat):V) xs)=instructionValue inst xs := by
  rw [step_at i hi,hb]
  rfl
#print axioms drain_formula
#print axioms literal_step
end PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource

