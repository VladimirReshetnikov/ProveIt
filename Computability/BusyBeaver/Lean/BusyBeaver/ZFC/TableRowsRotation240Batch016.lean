import BusyBeaver.ZFC.CountedTreeRotation240
import BusyBeaver.ZFC.ControlTableBinding
import BusyBeaver.ZFC.BisimCertRotation240

set_option autoImplicit false

/-! Fresh packed-row equality obligations. Historical binary coverage supplies only partition data. -/
namespace SetTheory.BusyBeaver.ZFC.TableRowsRotation240
open SiteCoverage ControlTableBinding

theorem block_512 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, true, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false]) = true := by
  decide +kernel

theorem block_513 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, true, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]) = true := by
  decide +kernel

theorem block_514 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, true]) = true := by
  decide +kernel

theorem block_515 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, true, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, true, false]) = true := by
  decide +kernel

theorem block_516 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, true, true, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, true, true, false]) = true := by
  decide +kernel

theorem block_517 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, true, true, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, true, true, true]) = true := by
  decide +kernel

theorem block_518 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, true]) = true := by
  decide +kernel

theorem block_519 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, true, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, true, false]) = true := by
  decide +kernel

theorem block_520 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, true, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, true, true]) = true := by
  decide +kernel

theorem block_521 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, true]) = true := by
  decide +kernel

theorem block_522 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, true, false, false, false, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, true, false, false, false, false]) = true := by
  decide +kernel

theorem block_523 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, true, false, false, false, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, true, false, false, false, true]) = true := by
  decide +kernel

theorem block_524 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, true, false, false, true, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, true, false, false, true, false]) = true := by
  decide +kernel

theorem block_525 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, true, false, false, true, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, true, false, false, true, true]) = true := by
  decide +kernel

theorem block_526 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, true, false, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, true, false, true]) = true := by
  decide +kernel

theorem block_527 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, true, true, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, true, true, false]) = true := by
  decide +kernel

theorem block_528 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, true, true, true, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, true, true, true, false]) = true := by
  decide +kernel

theorem block_529 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, true, true, true, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, true, true, true, true]) = true := by
  decide +kernel

end SetTheory.BusyBeaver.ZFC.TableRowsRotation240
