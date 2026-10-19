import BusyBeaver.ZFC.TableRowsRotation240

set_option autoImplicit false

open SetTheory.BusyBeaver.ZFC
open SiteCoverage ControlTableBinding

#print axioms SetTheory.BusyBeaver.ZFC.TableRowsRotation240.all_rows
example :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) [] TreeRotation240.tree = true := SetTheory.BusyBeaver.ZFC.TableRowsRotation240.all_rows

#print axioms SetTheory.BusyBeaver.ZFC.TableRowsRotation240.table_eq
example :
    PackedTables.table BisimCertRotation240.tableR BisimCertRotation240.countR =
    (ControlCatalogue.leafEntries TreeRotation240.tree).map
      (ArithmeticControlTable.rowOf TreeRotation240.tree) := SetTheory.BusyBeaver.ZFC.TableRowsRotation240.table_eq

