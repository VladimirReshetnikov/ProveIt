import BusyBeaver.ZFC.ArithmeticDagControlPerm222

set_option autoImplicit false

namespace SetTheory.BusyBeaver.ZFC.ArithmeticDagControlPerm222Checks

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticDagControlPerm222
open ArithmeticControlFile (regValue liveValue)

example : path.root = 0 := rfl
example : path.nnodes = 487 := rfl
example : table.length = 4751 := table_length
example : ArithmeticDagRun.Occ DagPerm.dagPerm rowsLit 488 (.node 0) 1 rootExit := root_occ
example : table = (ControlCatalogue.leafEntries (RMBisim.ptree path)).map
    (ArithmeticControlTable.rowOf (RMBisim.ptree path)) := table_eq_catalogue

section Model

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example : 𝚺₁-Function₂[V] run := inferInstance

/-- A real instruction of the complete table, without an occurrence premise. -/
theorem first_zero_step (x : V) (hz : regValue x 1 = 0) :
    run 1 (liveValue 1 x) = liveValue 3 x := by
  rw [run_one]
  simpa [ArithmeticControlBisim.sem, hz] using spec 1 ⟨2, 1, 3, 2⟩ x first_row

example {x y : V}
    (h : ArithmeticDagRun.IRun DagPerm.dagPerm rowsLit run (.node 0) x .normal y) :
    ∃ t : V, run t (liveValue 1 x) = liveValue 1 y := root_reach_normal h

example {x y : V}
    (h : ArithmeticDagRun.IRun DagPerm.dagPerm rowsLit run (.node 0) x .halt y) :
    ∃ t : V, run t (liveValue 1 x) = 0 := root_reach_halt h

end Model

#print axioms table_eq_catalogue
#print axioms packedRows_bound
#print axioms root_occB
#print axioms root_occ
#print axioms spec
#print axioms run_zero
#print axioms run_one
#print axioms run_add
#print axioms run_halted
#print axioms root_reach_normal
#print axioms root_reach_halt
#print axioms first_zero_step

end SetTheory.BusyBeaver.ZFC.ArithmeticDagControlPerm222Checks
