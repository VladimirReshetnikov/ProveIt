import BusyBeaver.ZFC.CountedTreeRotation240
import BusyBeaver.ZFC.ControlTableBinding
import BusyBeaver.ZFC.BisimCertRotation240

set_option autoImplicit false

/-! Fresh packed-row equality obligations. Historical binary coverage supplies only partition data. -/
namespace SetTheory.BusyBeaver.ZFC.TableRowsRotation240
open SiteCoverage ControlTableBinding

theorem block_0 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([false] : List Bool).reverse (descend TreeRotation240.tree [false]) = true := by
  decide +kernel

theorem block_1 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, false] : List Bool).reverse (descend TreeRotation240.tree [true, false]) = true := by
  decide +kernel

theorem block_2 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, false]) = true := by
  decide +kernel

theorem block_3 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, false]) = true := by
  decide +kernel

theorem block_4 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, false]) = true := by
  decide +kernel

theorem block_5 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, false]) = true := by
  decide +kernel

theorem block_6 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, false, false, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, false, false]) = true := by
  decide +kernel

theorem block_7 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, false, false, true, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, false, true, false]) = true := by
  decide +kernel

theorem block_8 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, false, false, true, true, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, false, true, true, false]) = true := by
  decide +kernel

theorem block_9 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, false, false, true, true, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, false, true, true, true]) = true := by
  decide +kernel

theorem block_10 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, false, true, false, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, true, false, false]) = true := by
  decide +kernel

theorem block_11 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, false, true, false, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, true, false, true]) = true := by
  decide +kernel

theorem block_12 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, false, true, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, true, true]) = true := by
  decide +kernel

theorem block_13 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, false]) = true := by
  decide +kernel

theorem block_14 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, false, false, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, false, false, false]) = true := by
  decide +kernel

theorem block_15 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, false, false, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, false, false, true]) = true := by
  decide +kernel

theorem block_16 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, false, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, false, true]) = true := by
  decide +kernel

theorem block_17 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, true, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, true, false]) = true := by
  decide +kernel

theorem block_18 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, true, true, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, true, true, false]) = true := by
  decide +kernel

theorem block_19 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, true, true, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, true, true, true]) = true := by
  decide +kernel

theorem block_20 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, false]) = true := by
  decide +kernel

theorem block_21 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, true]) = true := by
  decide +kernel

theorem block_22 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, false]) = true := by
  decide +kernel

theorem block_23 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, true]) = true := by
  decide +kernel

theorem block_24 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, false]) = true := by
  decide +kernel

theorem block_25 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, true]) = true := by
  decide +kernel

theorem block_26 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, false]) = true := by
  decide +kernel

theorem block_27 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, true]) = true := by
  decide +kernel

theorem block_28 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, true, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, true, false]) = true := by
  decide +kernel

theorem block_29 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, true, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, true, true]) = true := by
  decide +kernel

theorem block_30 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, false, false, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, false, false, false]) = true := by
  decide +kernel

theorem block_31 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, false, false, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, false, false, true]) = true := by
  decide +kernel

end SetTheory.BusyBeaver.ZFC.TableRowsRotation240
