import BusyBeaver.ZFC.ArithmeticControlTree
import BusyBeaver.ZFC.TreeRotation240
import BusyBeaver.ZFC.Dag254
import BusyBeaver.ZFC.RMEquiv
import BusyBeaver.ZFC.BisimCertRotation240

set_option autoImplicit false

/-!
# Catalogue instances and initial certificate probes for Rotation240

Two instances of the tree-generic control interpreter `ArithmeticControlTree`:

* `dagTree`, the decoder tree of the path program `ofDag dag254 219`, i.e. the
  unfolding of the 219-node DAG on which the L2 subroutine proofs are stated;
* `TreeRotation240.tree`, the decoder tree of the rotated 240-state source.

The generated `BisimCertRotation240.certList` contains 3,862 entries. The
current source contains length/row probes and a kernel proof for entries
0–9. Complete chunk checking and instantiation of
`ArithmeticControlBisim.halts_iff_of_check` remain pending. The intended
conclusion relates halting in every `IΣ₁` model from every internal register
file. The certificate's ten unit-offset entries account for the two
transfer-plus-one loop rotations; the routing245 re-association needs none.

For the PA endpoint this is intended to replace the external chain
`SourceRotation240`/`SourceRotation244`/`BisimRouting245`/`Bisim254`.
-/

namespace SetTheory.BusyBeaver.ZFC.ControlBisimRotation240

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open RegisterPath RMBisim ControlCatalogue ArithmeticControlBisim ArithmeticControlTree
open ArithmeticControlFile (regValue fileValue liveValue reg_file live_ne_zero live_defined
  liveDef projectionDef projection_defined)

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The decoder tree of the dag254 path program (fuel as in its path semantics). -/
def dagTree : Tree := toTree (RMEquiv.ofDag Dag254.dag254 219) 220 Dag254.dag254.root

theorem dag_length : (leafEntries dagTree).length = 6460 := by
  rw [leafEntries_length]; decide +kernel

theorem rot_length : (leafEntries TreeRotation240.tree).length = 6455 := by
  rw [leafEntries_length]; decide +kernel

/-! ## Row tables as constants (evaluated once per kernel check) -/

def rowTreeD : BT Row := BT.ofList ((leafEntries dagTree).map (rowOf dagTree))
def rowTreeR : BT Row := BT.ofList ((leafEntries TreeRotation240.tree).map (rowOf TreeRotation240.tree))

def rowsD (c : Nat) : Option Row := if c = 0 then none else rowTreeD.get (c - 1)
def rowsR (c : Nat) : Option Row := if c = 0 then none else rowTreeR.get (c - 1)

theorem rowsD_eq : rowsD = rows dagTree := rfl
theorem rowsR_eq : rowsR = rows TreeRotation240.tree := rfl

def certTree : BT ArithmeticControlBisim.Entry := BT.ofList BisimCertRotation240.certList
def cert (i : Nat) : Option ArithmeticControlBisim.Entry := certTree.get i

abbrev chunk (start count : Nat) : Bool :=
  checkFrom rowsD rowsR cert BisimCertRotation240.fuel BisimCertRotation240.size start count

theorem rows_probe : (rowsD 6460).isSome && (rowsR 6455).isSome = true := by decide +kernel

theorem check_probe : chunk 0 10 = true := by decide +kernel

end SetTheory.BusyBeaver.ZFC.ControlBisimRotation240
