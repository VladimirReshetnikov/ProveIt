import BusyBeaver.ZFC.CountedTreeRotation240
import BusyBeaver.ZFC.ControlTableBinding
import BusyBeaver.ZFC.BisimCertRotation240
import BusyBeaver.ZFC.TableRowsRotation240Batch014
import BusyBeaver.ZFC.TableRowsRotation240Batch015
import BusyBeaver.ZFC.TableRowsRotation240Join000
import BusyBeaver.ZFC.TableRowsRotation240Join013

set_option autoImplicit false

/-! Fresh packed-row equality obligations. Historical binary coverage supplies only partition data. -/
namespace SetTheory.BusyBeaver.ZFC.TableRowsRotation240
open SiteCoverage ControlTableBinding

theorem join_448 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false, false, true, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false, false, true, true]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false, false, true, true] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false, false, true, true, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false, false, true, true, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_462 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_463

theorem join_449 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false, false, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false, false, true]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false, false, true] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false, false, true, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false, false, true, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_461 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_448

theorem join_450 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false, false]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false, false] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false, false, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false, false, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_460 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_449

theorem join_451 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false, true, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false, true, false]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false, true, false] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false, true, false, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false, true, false, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_464 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_465

theorem join_452 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false, true]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false, true] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false, true, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false, true, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_451 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_466

theorem join_453 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_450 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_452

theorem join_454 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, false, false, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, false, false, false]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, false, false, false] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, false, false, false, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, false, false, false, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_467 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_468

theorem join_455 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, false, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, false, false]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, false, false] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, false, false, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, false, false, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_454 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_469

theorem join_456 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, false, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, false, true]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, false, true] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, false, true, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, false, true, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_470 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_471

theorem join_457 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, false]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, false] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, false, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, false, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_455 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_456

theorem join_458 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, false, false, true, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, false, false, true, true]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, false, false, true, true] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, false, false, true, true, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, false, false, true, true, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_474 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_475

theorem join_459 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, false, false, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, false, false, true]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, false, false, true] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, false, false, true, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, false, false, true, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_473 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_458

theorem join_460 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, false, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, false, false]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, false, false] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, false, false, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, false, false, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_472 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_459

theorem join_461 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, false, true, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, false, true, false]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, false, true, false] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, false, true, false, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, false, true, false, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_476 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_477

theorem join_462 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, false, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, false, true]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, false, true] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, false, true, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, false, true, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_461 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_478

theorem join_463 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, false]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, false] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, false, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, false, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_460 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_462

theorem join_464 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_463 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_479

theorem join_465 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_457 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_464

theorem join_466 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_453 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_465

theorem join_467 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_447 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_466

theorem join_468 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_446 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_467

theorem join_469 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_23 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_468

theorem join_470 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, false]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, false] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, false, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, false, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_480 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_481

theorem join_471 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false, false, true, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false, false, true, true]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false, false, true, true] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false, false, true, true, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false, false, true, true, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_484 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_485

theorem join_472 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false, false, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false, false, true]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false, false, true] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false, false, true, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false, false, true, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_483 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_471

theorem join_473 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false, false]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false, false] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false, false, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false, false, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_482 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_472

theorem join_474 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false, true, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false, true, false]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false, true, false] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false, true, false, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false, true, false, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_486 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_487

theorem join_475 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false, true]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false, true] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false, true, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false, true, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_474 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_488

theorem join_476 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_473 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_475

theorem join_477 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_476 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_489

theorem join_478 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_470 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_477

theorem join_479 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, false, false, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, false, false, false]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, false, false, false] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, false, false, false, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, false, false, false, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_490 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_491

end SetTheory.BusyBeaver.ZFC.TableRowsRotation240
