import BusyBeaver.ZFC.TableRowsRotation240Batch000

set_option autoImplicit false

open SetTheory.BusyBeaver.ZFC
open SiteCoverage ControlTableBinding

#print axioms SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_0
example :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([false] : List Bool).reverse (descend TreeRotation240.tree [false]) = true := SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_0

#print axioms SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_1
example :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, false] : List Bool).reverse (descend TreeRotation240.tree [true, false]) = true := SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_1

#print axioms SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_2
example :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, false]) = true := SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_2

#print axioms SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_3
example :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, false]) = true := SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_3

#print axioms SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_4
example :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, false]) = true := SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_4

#print axioms SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_5
example :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, false]) = true := SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_5

#print axioms SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_6
example :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, false, false, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, false, false]) = true := SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_6

#print axioms SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_7
example :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, false, false, true, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, false, true, false]) = true := SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_7

#print axioms SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_8
example :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, false, false, true, true, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, false, true, true, false]) = true := SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_8

#print axioms SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_9
example :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, false, false, true, true, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, false, true, true, true]) = true := SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_9

#print axioms SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_10
example :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, false, true, false, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, true, false, false]) = true := SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_10

#print axioms SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_11
example :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, false, true, false, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, true, false, true]) = true := SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_11

#print axioms SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_12
example :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, false, true, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, true, true]) = true := SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_12

#print axioms SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_13
example :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, false]) = true := SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_13

#print axioms SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_14
example :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, false, false, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, false, false, false]) = true := SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_14

#print axioms SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_15
example :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, false, false, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, false, false, true]) = true := SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_15

#print axioms SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_16
example :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, false, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, false, true]) = true := SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_16

#print axioms SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_17
example :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, true, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, true, false]) = true := SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_17

#print axioms SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_18
example :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, true, true, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, true, true, false]) = true := SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_18

#print axioms SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_19
example :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, true, true, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, true, true, true]) = true := SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_19

#print axioms SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_20
example :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, false]) = true := SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_20

#print axioms SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_21
example :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, true]) = true := SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_21

#print axioms SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_22
example :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, false]) = true := SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_22

#print axioms SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_23
example :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, true]) = true := SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_23

#print axioms SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_24
example :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, false]) = true := SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_24

#print axioms SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_25
example :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, true]) = true := SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_25

#print axioms SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_26
example :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, false]) = true := SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_26

#print axioms SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_27
example :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, true]) = true := SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_27

#print axioms SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_28
example :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, true, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, true, false]) = true := SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_28

#print axioms SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_29
example :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, true, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, true, true]) = true := SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_29

#print axioms SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_30
example :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, false, false, false] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, false, false, false]) = true := SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_30

#print axioms SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_31
example :
    allSites (checkRow CountedTreeRotation240.counted (PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR)) ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, false, false, true] : List Bool).reverse (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, false, false, true]) = true := SetTheory.BusyBeaver.ZFC.TableRowsRotation240.block_31

