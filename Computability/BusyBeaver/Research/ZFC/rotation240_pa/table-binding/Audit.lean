import BusyBeaver.ZFC.ControlTableBinding

set_option autoImplicit false

open SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage ControlCatalogue ArithmeticControlTable
open ArithmeticControlBisim (Row)

#print axioms ControlTableBinding.rowCounted_annotate
#print axioms ControlTableBinding.crank_at_get
#print axioms ControlTableBinding.checked_row_at_index
#print axioms ControlTableBinding.packed_table_eq
#print axioms ControlTableBinding.checked_rank_resolves
#print axioms ControlTableBinding.checked_row_at_walk

example (t : Tree) (entry : List Bool × Edge) :
    ControlTableBinding.rowCounted (annotate t) entry = rowOf t entry :=
  ControlTableBinding.rowCounted_annotate t entry

example (t : Tree) (i : Nat) (hi : i < (leafEntries t).length) :
    crank (annotate t) ((getElem (leafEntries t) i hi)).1 = i :=
  ControlTableBinding.crank_at_get t i hi

example (t : Tree) (ct : ControlCatalogue.CTree) (rows : Nat → Option Row)
    (hct : ct = annotate t)
    (h : allSites (ControlTableBinding.checkRow ct rows) [] t = true)
    (i : Nat) (hi : i < (leafEntries t).length) :
    rows (i + 1) = some (rowOf t ((getElem (leafEntries t) i hi))) :=
  ControlTableBinding.checked_row_at_index t ct rows hct h i hi

example (t : Tree) (ct : ControlCatalogue.CTree) (n count : Nat)
    (hct : ct = annotate t) (hc : count = (leafEntries t).length)
    (h : allSites (ControlTableBinding.checkRow ct (PackedTables.rowsOf n count)) [] t = true) :
    PackedTables.table n count = (leafEntries t).map (rowOf t) :=
  ControlTableBinding.packed_table_eq t ct n count hct hc h

example (t : Tree) (ct : ControlCatalogue.CTree) (rows : Nat → Option Row)
    (hct : ct = annotate t)
    (h : allSites (ControlTableBinding.checkRow ct rows) [] t = true)
    (P : List Bool) :
    ∃ e d, ∃ hr : crank ct P < (leafEntries t).length,
      twalk t P 0 = some (e, d) ∧
      getElem (leafEntries t) (crank ct P) hr = (consume P d, e) :=
  ControlTableBinding.checked_rank_resolves t ct rows hct h P

example (t : Tree) (ct : ControlCatalogue.CTree) (rows : Nat → Option Row)
    (hct : ct = annotate t)
    (h : allSites (ControlTableBinding.checkRow ct rows) [] t = true)
    (P : List Bool) (r : Nat) (positive : Bool) :
    ∃ e d, ∃ hr : crank ct (outgoingPathOf P (.decnz r) positive) < (leafEntries t).length,
      twalk t (outgoingPathOf P (.decnz r) positive) 0 = some (e, d) ∧
      getElem (leafEntries t) (crank ct (outgoingPathOf P (.decnz r) positive)) hr =
        (consume (outgoingPathOf P (.decnz r) positive) d, e) :=
  ControlTableBinding.checked_rank_resolves t ct rows hct h _

example (t : Tree) (ct : ControlCatalogue.CTree) (rows : Nat → Option Row)
    (hct : ct = annotate t)
    (h : allSites (ControlTableBinding.checkRow ct rows) [] t = true)
    (P : List Bool) (e : Edge) (d : Nat) (hw : twalk t P 0 = some (e, d)) :
    rows (crank (annotate t) (consume P d) + 1) = some (rowOf t (consume P d, e)) :=
  ControlTableBinding.checked_row_at_walk t ct rows hct h P e d hw

example (ct : ControlCatalogue.CTree) (P : List Bool) (r : Nat) :
    (ControlTableBinding.rowCounted ct (P, .inc r)).reg.val =
      Permutation252Frame.physOf r := rfl

example (ct : ControlCatalogue.CTree) (P : List Bool) :
    (ControlTableBinding.rowCounted ct (P, .halt)).next0 = 0 ∧
    (ControlTableBinding.rowCounted ct (P, .halt)).next1 = 0 := ⟨rfl, rfl⟩
