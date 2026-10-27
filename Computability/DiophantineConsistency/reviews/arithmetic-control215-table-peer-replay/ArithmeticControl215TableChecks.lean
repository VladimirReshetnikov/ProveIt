import BusyBeaver.ZFC.ArithmeticControl215Table

set_option autoImplicit false
set_option Elab.async false

namespace SetTheory.BusyBeaver.ZFC.ArithmeticControl215TableChecks

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticControl215Table
open ArithmeticControlFile (regValue liveValue)

example : path = KSource215.p215 := rfl
example : path.root = 178 := rfl
example : path.nnodes = 179 := rfl
example : table215.length = 4751 := table215_length
example : packed215 < 2 ^ (36 * count) := packed215_bound
example : table215 = (ControlCatalogue.leafEntries KSource215.t215).map
    (ArithmeticControlTable.rowOf KSource215.t215) := table215_eq_catalogue

section Model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example : 𝚺₁-Function₂[V] run215 := inferInstance

theorem first_zero_step (x : V) (hz : regValue x 1 = 0) :
    run215 1 (liveValue 1 x) = liveValue 3 x := by
  rw [run215_one]
  simpa [ArithmeticControlBisim.sem, hz] using spec215 1 ⟨2, 1, 3, 2⟩ x first_row

example (t u x : V) : run215 (t + u) x = run215 u (run215 t x) := run215_add t u x
example (t : V) : run215 t 0 = 0 := run215_halted t
end Model

#print axioms packed215_bound
#print axioms table215_length
#print axioms table215_eq_catalogue
#print axioms spec215
#print axioms run215_zero
#print axioms run215_one
#print axioms run215_add
#print axioms run215_halted
#print axioms first_zero_step

end SetTheory.BusyBeaver.ZFC.ArithmeticControl215TableChecks
