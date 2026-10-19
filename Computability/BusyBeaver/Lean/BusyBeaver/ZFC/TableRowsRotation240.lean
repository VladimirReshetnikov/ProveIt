import BusyBeaver.ZFC.CountedTreeRotation240
import BusyBeaver.ZFC.ControlTableBinding
import BusyBeaver.ZFC.BisimCertRotation240
import BusyBeaver.ZFC.TableRowsRotation240Join016

set_option autoImplicit false

/-! Fresh packed-row equality obligations. Historical binary coverage supplies only partition data. -/
namespace SetTheory.BusyBeaver.ZFC.TableRowsRotation240
open SiteCoverage ControlTableBinding

theorem all_rows :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) [] TreeRotation240.tree = true := SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_528

theorem table_eq :
    PackedTables.table BisimCertRotation240.tableR BisimCertRotation240.countR =
    (ControlCatalogue.leafEntries TreeRotation240.tree).map
      (ArithmeticControlTable.rowOf TreeRotation240.tree) := ControlTableBinding.packed_table_eq TreeRotation240.tree CountedTreeRotation240.counted
  BisimCertRotation240.tableR BisimCertRotation240.countR
  CountedTreeRotation240.counted_eq
  (by simpa only [BisimCertRotation240.countR] using CountedTreeRotation240.catalogue_length.symm)
  all_rows

end SetTheory.BusyBeaver.ZFC.TableRowsRotation240
