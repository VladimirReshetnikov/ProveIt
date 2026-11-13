module
public import PA196.Arithmetic.Scheduler.Base
public import PA196.Program
public import PA196.Source.Readers
public import PA196.Arithmetic.Machine.PATheory
public import PA196.Arithmetic.Scheduler.InternalCodedSourceCopy
@[expose] public section
open PA196.Arithmetic.Machine.PA
namespace PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource
open M6 M6.PA PA196.Arithmetic PA196.Arithmetic.Scheduler
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* PA196.Arithmetic.Machine.PA.theory]
lemma copyEnd_valid (r : Fin 9) (n xs : V) (hv : ValidStore xs) : ValidStore (copyEnd r n xs) :=
  drainEnd_valid 6 r n _ (drainTwoEnd_valid r 1 6 n xs hv)
#print axioms copyEnd_valid
end PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource

