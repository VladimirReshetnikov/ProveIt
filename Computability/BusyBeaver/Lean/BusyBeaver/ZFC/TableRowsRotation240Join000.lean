import BusyBeaver.ZFC.CountedTreeRotation240
import BusyBeaver.ZFC.ControlTableBinding
import BusyBeaver.ZFC.BisimCertRotation240
import BusyBeaver.ZFC.TableRowsRotation240Batch000
import BusyBeaver.ZFC.TableRowsRotation240Batch001

set_option autoImplicit false

/-! Fresh packed-row equality obligations. Historical binary coverage supplies only partition data. -/
namespace SetTheory.BusyBeaver.ZFC.TableRowsRotation240
open SiteCoverage ControlTableBinding

theorem join_0 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, false, false, true, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, false, true, true]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, false, false, true, true] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, false, true, true, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, false, true, true, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_8 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_9

theorem join_1 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, false, false, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, false, true]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, false, false, true] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, false, true, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, false, true, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_7 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_0

theorem join_2 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, false, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, false]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, false, false] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, false, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, false, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_6 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_1

theorem join_3 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, false, true, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, true, false]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, false, true, false] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, true, false, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, true, false, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_10 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_11

theorem join_4 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, false, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, true]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, false, true] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, true, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, true, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_3 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_12

theorem join_5 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, false]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, false] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_2 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_4

theorem join_6 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, false, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, false, false]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, false, false] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, false, false, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, false, false, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_14 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_15

theorem join_7 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, false]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, false] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, false, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, false, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_6 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_16

theorem join_8 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, true, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, true, true]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, true, true] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, true, true, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, true, true, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_18 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_19

theorem join_9 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, true]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, true] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, true, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, true, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_17 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_8

theorem join_10 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_7 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_9

theorem join_11 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_20 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_21

theorem join_12 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_22 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_23

theorem join_13 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_11 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_12

theorem join_14 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_10 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_13

theorem join_15 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_13 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_14

theorem join_16 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_24 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_25

theorem join_17 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_26 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_27

theorem join_18 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_16 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_17

theorem join_19 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, true]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, true] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, true, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, true, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_28 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_29

theorem join_20 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_18 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_19

theorem join_21 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, false, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, false, false]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, false, false] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, false, false, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, false, false, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_30 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_31

theorem join_22 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, false, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, false, true]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, false, true] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, false, true, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, false, true, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_32 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_33

theorem join_23 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, false]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, false] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, false, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, false, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_21 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_22

theorem join_24 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, false, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, false, false]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, false, false] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, false, false, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, false, false, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_34 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_35

theorem join_25 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, false, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, false, true]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, false, true] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, false, true, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, false, true, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_36 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_37

theorem join_26 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, false]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, false] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, false, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, false, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_24 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_25

theorem join_27 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, false]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, false] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, false, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, false, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_38 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_39

theorem join_28 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_40 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_41

theorem join_29 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, true, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, true, false]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, true, false] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, true, false, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, true, false, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_42 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_43

theorem join_30 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, true, true, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, true, true, false]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, true, true, false] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, true, true, false, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, true, true, false, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_44 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_45

theorem join_31 :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, true, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, true, true]) = true := allSites_join (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, true, true] : List Bool).reverse
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, true, true, false])
  (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, true, true, true])
  SetTheory.BusyBeaver.ZFC.TableRowsRotation240.join_30 SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_46

end SetTheory.BusyBeaver.ZFC.TableRowsRotation240
