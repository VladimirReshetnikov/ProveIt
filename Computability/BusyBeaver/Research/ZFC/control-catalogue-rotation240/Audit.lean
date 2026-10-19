import BusyBeaver.ZFC.ControlCatalogueRotation240

open SetTheory.BusyBeaver.ZFC
open RegisterPath ControlCatalogueRotation240

#print axioms SetTheory.BusyBeaver.ZFC.ControlCatalogueRotation240.table_eq
#print axioms SetTheory.BusyBeaver.ZFC.ControlCatalogueRotation240.table_length
#print axioms SetTheory.BusyBeaver.ZFC.ControlCatalogueRotation240.source_accepted
#print axioms SetTheory.BusyBeaver.ZFC.ControlCatalogueRotation240.source_length
#print axioms SetTheory.BusyBeaver.ZFC.ControlCatalogueRotation240.source_not_node
#print axioms SetTheory.BusyBeaver.ZFC.ControlCatalogueRotation240.source_walk
#print axioms SetTheory.BusyBeaver.ZFC.ControlCatalogueRotation240.source_rank
#print axioms SetTheory.BusyBeaver.ZFC.ControlCatalogueRotation240.rows_at
#print axioms SetTheory.BusyBeaver.ZFC.ControlCatalogueRotation240.table_row_at
#print axioms SetTheory.BusyBeaver.ZFC.ControlCatalogueRotation240.resolve_source
#print axioms SetTheory.BusyBeaver.ZFC.ControlCatalogueRotation240.resolve_source_self
#print axioms SetTheory.BusyBeaver.ZFC.ControlCatalogueRotation240.resolve_number_valid
#print axioms SetTheory.BusyBeaver.ZFC.ControlCatalogueRotation240.resolved_path
#print axioms SetTheory.BusyBeaver.ZFC.ControlCatalogueRotation240.nextControl_number
#print axioms SetTheory.BusyBeaver.ZFC.ControlCatalogueRotation240.nextControl_resolves
#print axioms SetTheory.BusyBeaver.ZFC.ControlCatalogueRotation240.sourcePC_cast

example : table = actualEntries.map (ArithmeticControlTable.rowOf TreeRotation240.tree) :=
  table_eq
example : table.length = 6455 := table_length
example (i : Control) : SiteRotation240.checkSite (source i).1 (source i).2 = true :=
  source_accepted i
example (i : Control) : (source i).1.length ≤ 64 := source_length i
example (i : Control) (n : Nat) : (source i).2 ≠ .node n := source_not_node i n
example (i : Control) :
    walk SourceRotation240.program (SourceRotation240.program.nnodes + 1)
      SourceRotation240.program.root (source i).1 0 =
      some ((source i).2, (source i).1.length) := source_walk i
example (i : Control) :
    ControlCatalogue.crank CountedTreeRotation240.counted (source i).1 = i.val := source_rank i
example (i : Control) :
    rows (number i) = some (ArithmeticControlTable.rowOf TreeRotation240.tree (source i)) := rows_at i
example (i : Control) :
    getElem? table i.val = some (ArithmeticControlTable.rowOf TreeRotation240.tree (source i)) :=
  table_row_at i
example (P : List Bool) (e : Edge) (d : Nat)
    (hw : walk SourceRotation240.program (SourceRotation240.program.nnodes + 1)
      SourceRotation240.program.root P 0 = some (e, d)) :
    source (resolveControl P) = (consume P d, e) := resolve_source P e d hw
example (i : Control) : resolveControl (source i).1 = i := resolve_source_self i
example (P : List Bool) :
    0 < number (resolveControl P) ∧ number (resolveControl P) ≤ 6455 := resolve_number_valid P
example (P : List Bool) :
    ∃ e d, walk SourceRotation240.program (SourceRotation240.program.nnodes + 1)
        SourceRotation240.program.root P 0 = some (e, d) ∧
      source (resolveControl P) = (consume P d, e) ∧
      SiteRotation240.checkSite (consume P d) e = true := resolved_path P
example (i : Control) (positive : Bool) (h : (source i).2 ≠ .halt) :
    nextControl i positive = number (resolveControl
      (ArithmeticControlTable.outgoingPathOf (source i).1 (source i).2 positive)) :=
  nextControl_number i positive h
example (i : Control) (positive : Bool) (h : (source i).2 ≠ .halt) :
    ∃ j : Control, nextControl i positive = number j ∧
      ∃ e d, walk SourceRotation240.program (SourceRotation240.program.nnodes + 1)
          SourceRotation240.program.root
          (ArithmeticControlTable.outgoingPathOf (source i).1 (source i).2 positive) 0 =
          some (e, d) ∧
        source j = (consume
          (ArithmeticControlTable.outgoingPathOf (source i).1 (source i).2 positive) d, e) :=
  nextControl_resolves i positive h

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
example {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] (i : Control) :
    (sourcePC i : V) = ArithmeticControlTable.binaryValue (source i).1 := sourcePC_cast i
