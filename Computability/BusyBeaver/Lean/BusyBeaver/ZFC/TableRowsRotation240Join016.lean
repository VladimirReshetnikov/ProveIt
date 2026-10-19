import BusyBeaver.ZFC.CountedTreeRotation240
import BusyBeaver.ZFC.ControlTableBinding
import BusyBeaver.ZFC.BisimCertRotation240
import BusyBeaver.ZFC.TableRowsRotation240Batch000
import BusyBeaver.ZFC.TableRowsRotation240Batch016
import BusyBeaver.ZFC.TableRowsRotation240Join015

set_option autoImplicit false

/-! Fresh packed-row equality obligations. Historical binary coverage supplies only partition data. -/
namespace SetTheory.BusyBeaver.ZFC.TableRowsRotation240
open SiteCoverage ControlTableBinding

theorem join_512 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_511 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_518

theorem join_513 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_4 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_512

theorem join_514 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, true]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, true] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, true, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, true, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_519 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_520

theorem join_515 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_513 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_514

theorem join_516 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false])
  (descend TreeRotation240.tree [true, true, true, false, true, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_515 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_521

theorem join_517 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, false])
  (descend TreeRotation240.tree [true, true, true, false, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_3 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_516

theorem join_518 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, true, false, false, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, true, false, false, false]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, true, false, false, false] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, true, false, false, false, false])
  (descend TreeRotation240.tree [true, true, true, true, false, false, false, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_522 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_523

theorem join_519 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, true, false, false, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, true, false, false, true]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, true, false, false, true] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, true, false, false, true, false])
  (descend TreeRotation240.tree [true, true, true, true, false, false, true, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_524 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_525

theorem join_520 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, true, false, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, true, false, false]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, true, false, false] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, true, false, false, false])
  (descend TreeRotation240.tree [true, true, true, true, false, false, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_518 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_519

theorem join_521 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, true, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, true, false]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, true, false] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, true, false, false])
  (descend TreeRotation240.tree [true, true, true, true, false, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_520 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_526

theorem join_522 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, true, true, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, true, true, true]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, true, true, true] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, true, true, true, false])
  (descend TreeRotation240.tree [true, true, true, true, true, true, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_528 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_529

theorem join_523 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, true, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, true, true]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, true, true] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, true, true, false])
  (descend TreeRotation240.tree [true, true, true, true, true, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_527 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_522

theorem join_524 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, true]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, true] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, true, false])
  (descend TreeRotation240.tree [true, true, true, true, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_521 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_523

theorem join_525 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false])
  (descend TreeRotation240.tree [true, true, true, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_517 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_524

theorem join_526 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true] : List Bool).reverse (descend TreeRotation240.tree [true, true]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, false])
  (descend TreeRotation240.tree [true, true, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_2 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_525

theorem join_527 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true] : List Bool).reverse (descend TreeRotation240.tree [true]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true] : List Bool).reverse
  (descend TreeRotation240.tree [true, false])
  (descend TreeRotation240.tree [true, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_1 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_526

theorem join_528 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([] : List Bool).reverse (descend TreeRotation240.tree []) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([] : List Bool).reverse
  (descend TreeRotation240.tree [false])
  (descend TreeRotation240.tree [true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_0 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_527

end SetTheory.BusyBeaver.ZFC.TableRowsRotation240
