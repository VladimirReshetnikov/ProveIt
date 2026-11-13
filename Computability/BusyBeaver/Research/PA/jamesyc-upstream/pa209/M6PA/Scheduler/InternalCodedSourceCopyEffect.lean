module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.InternalCodedSourceCopy
@[expose] public section
open M6.Arithmetic.PA
namespace M6.Arithmetic.PA.InternalTrace.CodedSource
open M6 M6.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
lemma copyEnd_valid (r : Fin 9) (n xs : V) (hv : ValidStore xs) : ValidStore (copyEnd r n xs) :=
  drainEnd_valid 6 r n _ (drainTwoEnd_valid r 1 6 n xs hv)
#print axioms copyEnd_valid
end M6.Arithmetic.PA.InternalTrace.CodedSource

