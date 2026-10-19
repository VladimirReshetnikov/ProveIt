import BusyBeaver.ZFC.ControlTableBinding
import BusyBeaver.ZFC.BisimCertRotation240
import BusyBeaver.ZFC.CountedTreeRotation240

set_option autoImplicit false

/-! Measured pilot for exact packed rows at one complete decoder cutPath.
The 20 leaves are one cut of the existing partition; its previous binary-site
proof is not reused as proof of this different row-equality proposition.
No full-table equality or binary simulation is asserted by this pilot. -/
namespace SetTheory.BusyBeaver.ZFC.TableRowsRotation240Pilot
open SiteCoverage ControlTableBinding

def cutPath : List Bool := [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false, true, true, false]

abbrev check := checkRow CountedTreeRotation240.counted
  (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)

theorem checked :
    allSites check cutPath.reverse (descend TreeRotation240.tree cutPath) = true := by
  decide +kernel

end SetTheory.BusyBeaver.ZFC.TableRowsRotation240Pilot
