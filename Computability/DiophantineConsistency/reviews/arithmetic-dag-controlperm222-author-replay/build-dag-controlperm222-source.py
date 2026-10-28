from pathlib import Path
import runpy,contextlib,io,hashlib
R=Path('/home/codex/.codex/worktrees/46be/Proofs');B=R/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC'
with contextlib.redirect_stdout(io.StringIO()): audit=runpy.run_path('/tmp/c222-dagperm-table-plan-audit.py')
packed=audit['packed'];rows=audit['pathRows']
assert len(rows)==4751 and packed.bit_length()==171033
text='''import BusyBeaver.ZFC.ArithmeticDagLoops
import BusyBeaver.ZFC.PackedTables

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-!
# The actual DagPerm control catalogue and root occurrence

The fixed packed table below contains all 4,751 rows of the current DagPerm
path catalogue. The two finite checks bind it both to the actual path tree
and to the complete structured root occurrence. The root is node 0; 487 is
the node-count argument, and the occurrence uses fuel 488. Normal exits
restart at positive control 1; halt reaches absorbing zero.

The represented run and root-exit adapters use these unconditional checks.
They do not assert a structured root run, an EnumStep simulation, a p215
machine simulation, source-ZFC calibration, or an HA proof endpoint.
-/

namespace SetTheory.BusyBeaver.ZFC.ArithmeticDagControlPerm222

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticControlBisim (Row sem)
open ArithmeticControlFile (regValue liveValue)
open ArithmeticControlTable (write)

/-- All actual rows, in 36-bit slots; generated from the current literal nodes. -/
def packedRows : Nat := PACKED_LITERAL

def count : Nat := 4751

def table : List Row := PackedTables.table packedRows count

def rowsLit (c : Nat) : Option Row := PackedTables.rowsOf packedRows count c

/-- Exactly the expression defining the existing pathDagPerm, without its
large unrelated certificate-data import. -/
def path : RegisterPath.Program := RMEquiv.ofDag DagPerm.dagPerm 487

/-- Complete current catalogue identity, checked in the kernel. -/
theorem table_eq_catalogue :
    table = (ControlCatalogue.leafEntries (RMBisim.ptree path)).map
      (ArithmeticControlTable.rowOf (RMBisim.ptree path)) := by
  decide +kernel

theorem table_length : table.length = 4751 := PackedTables.table_length _ _

/-- Every ordinary root exit restarts the literal interpreter. -/
def rootExit (_ : RMDag.Exit) : Nat := 1

theorem root_exit_positive (e : RMDag.Exit) : 0 < rootExit e := by decide

/-- No occurrence assumption: every row of the actual whole root is checked. -/
theorem root_occB :
    ArithmeticDagRun.occB DagPerm.dagPerm rowsLit 488 (.node 0) 1 rootExit = true := by
  decide +kernel

theorem root_occ :
    ArithmeticDagRun.Occ DagPerm.dagPerm rowsLit 488 (.node 0) 1 rootExit :=
  ArithmeticDagRun.occ_of_occB _ _ 488 _ 1 _ root_occB

theorem first_row : rowsLit 1 = some ⟨2, 1, 3, 2⟩ := by decide +kernel

section Model

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Fixed genuine represented internal run of the actual table. -/
noncomputable abbrev run (t x : V) : V := ArithmeticControlTable.controlRun table t x

theorem spec (c : Nat) (row : Row) (x : V) (h : rowsLit c = some row) :
    ArithmeticControlTable.stepValue table (liveValue (c : V) x) =
      sem regValue write liveValue row x := by
  obtain ⟨hc, hg⟩ := PackedTables.rowsOf_some packedRows count c row h
  exact ArithmeticControlTable.spec_get table c row x hc hg

theorem run_zero (x : V) : run 0 x = x := ArithmeticControlTable.controlRun_zero table x

theorem run_one (x : V) : run 1 x = ArithmeticControlTable.stepValue table x :=
  ArithmeticControlTable.controlRun_one table x

theorem run_add (t u x : V) : run (t + u) x = run u (run t x) :=
  ArithmeticControlTable.controlRun_add table t u x

theorem run_halted (t : V) : run t 0 = 0 := ArithmeticControlTable.controlRun_halted table t

/-- Normal-return adapter; its structured-run premise remains explicit. -/
theorem root_reach_normal {x y : V}
    (h : ArithmeticDagRun.IRun DagPerm.dagPerm rowsLit run (.node 0) x .normal y) :
    ∃ t : V, run t (liveValue 1 x) = liveValue 1 y := by
  simpa only [ArithmeticDagRun.Reach, rootExit] using h 488 1 rootExit root_occ

/-- Halt adapter, with absorbing zero rather than a live control numbered zero. -/
theorem root_reach_halt {x y : V}
    (h : ArithmeticDagRun.IRun DagPerm.dagPerm rowsLit run (.node 0) x .halt y) :
    ∃ t : V, run t (liveValue 1 x) = 0 := by
  simpa only [ArithmeticDagRun.Reach] using h 488 1 rootExit root_occ

end Model
end SetTheory.BusyBeaver.ZFC.ArithmeticDagControlPerm222
'''.replace('PACKED_LITERAL',hex(packed))
out=B/'ArithmeticDagControlPerm222.lean';assert not out.exists();out.write_text(text)
print('main',len(text.splitlines()),len(text),'packed bits',packed.bit_length(),hashlib.sha256(text.encode()).hexdigest())
