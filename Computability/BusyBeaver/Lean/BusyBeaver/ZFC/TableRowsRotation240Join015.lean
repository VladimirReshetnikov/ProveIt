import BusyBeaver.ZFC.CountedTreeRotation240
import BusyBeaver.ZFC.ControlTableBinding
import BusyBeaver.ZFC.BisimCertRotation240
import BusyBeaver.ZFC.TableRowsRotation240Batch000
import BusyBeaver.ZFC.TableRowsRotation240Batch015
import BusyBeaver.ZFC.TableRowsRotation240Batch016
import BusyBeaver.ZFC.TableRowsRotation240Join000
import BusyBeaver.ZFC.TableRowsRotation240Join014

set_option autoImplicit false

/-! Fresh packed-row equality obligations. Historical binary coverage supplies only partition data. -/
namespace SetTheory.BusyBeaver.ZFC.TableRowsRotation240
open SiteCoverage ControlTableBinding

theorem join_480 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, false, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, false, false]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, false, false] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, false, false, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, false, false, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_479 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_492

theorem join_481 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, false, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, false, true]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, false, true] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, false, true, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, false, true, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_493 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_494

theorem join_482 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, false]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, false] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, false, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, false, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_480 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_481

theorem join_483 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, false, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, false, true]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, false, true] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, false, true, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, false, true, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_496 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_497

theorem join_484 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, false]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, false] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, false, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, false, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_495 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_483

theorem join_485 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, true, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, true, false]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, true, false] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, true, false, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, true, false, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_498 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_499

theorem join_486 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, true, true, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, true, true, true]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, true, true, true] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, true, true, true, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, true, true, true, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_501 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_502

theorem join_487 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, true, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, true, true]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, true, true] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, true, true, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, true, true, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_500 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_486

theorem join_488 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, true]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, true] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, true, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, true, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_485 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_487

theorem join_489 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_484 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_488

theorem join_490 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false, false, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false, false, true]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false, false, true] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false, false, true, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false, false, true, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_504 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_505

theorem join_491 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false, false]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false, false] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false, false, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false, false, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_503 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_490

theorem join_492 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false, true, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false, true, false]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false, true, false] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false, true, false, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false, true, false, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_506 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_507

theorem join_493 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false, true, true, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false, true, true, true]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false, true, true, true] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false, true, true, true, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false, true, true, true, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_509 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_510

theorem join_494 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false, true, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false, true, true]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false, true, true] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false, true, true, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false, true, true, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_508 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_493

theorem join_495 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false, true]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false, true] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false, true, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false, true, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_492 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_494

theorem join_496 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_491 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_495

theorem join_497 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_496 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_511

theorem join_498 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_489 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_497

theorem join_499 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_482 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_498

theorem join_500 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_478 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_499

theorem join_501 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_469 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_500

theorem join_502 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_20 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_501

theorem join_503 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_15 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_502

theorem join_504 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, true] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_512 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_513

theorem join_505 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_503 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_504

theorem join_506 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_5 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_505

theorem join_507 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_506 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_514

theorem join_508 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_5 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_507

theorem join_509 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, true, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, true, true]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, true, true] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, true, true, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, true, true, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_516 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_517

theorem join_510 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, true]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, true] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, true, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, true, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_515 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_509

theorem join_511 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_508 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_510

end SetTheory.BusyBeaver.ZFC.TableRowsRotation240
