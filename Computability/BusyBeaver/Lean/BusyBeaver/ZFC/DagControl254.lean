import BusyBeaver.ZFC.ArithmeticControlTable
import BusyBeaver.ZFC.BisimCertRotation240

set_option autoImplicit false

/-!
# The represented dag254 control interpreter

The instance of `ArithmeticControlTable` at the packed 6,460-row table
`BisimCertRotation240.tableD`, the control catalogue of the path program
`ofDag dag254 219` (generated externally). The interpreter is defined by this
table alone: its use in the PA endpoint needs only two finite kernel checks on
literal data, the bisimulation with the Rotation240 interpreter
(`ControlBisimRotation240`) and the root occurrence of the dag254 program
(`DagRun254`); no decoder tree is evaluated by the kernel.
-/

namespace SetTheory.BusyBeaver.ZFC.DagControl254

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticControlBisim ArithmeticControlTable
open ArithmeticControlFile (regValue liveValue)

/-- The row table of the dag254 control interpreter. -/
abbrev table : List Row := PackedTables.table BisimCertRotation240.tableD BisimCertRotation240.countD

/-- Packed row lookup by control number. -/
abbrev rowsLit (c : Nat) : Option Row :=
  PackedTables.rowsOf BisimCertRotation240.tableD BisimCertRotation240.countD c

section Model

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The represented run of the dag254 control interpreter. -/
noncomputable abbrev run (t x : V) : V := controlRun table t x

theorem spec (c : Nat) (row : Row) (x : V) (h : rowsLit c = some row) :
    stepValue table (liveValue (c : V) x) = sem regValue write liveValue row x := by
  obtain ⟨hc, hg⟩ := PackedTables.rowsOf_some _ _ c row h
  exact spec_get table c row x hc hg

end Model

end SetTheory.BusyBeaver.ZFC.DagControl254
