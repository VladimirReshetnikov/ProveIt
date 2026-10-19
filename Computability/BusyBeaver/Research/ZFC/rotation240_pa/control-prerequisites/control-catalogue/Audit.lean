import BusyBeaver.ZFC.ControlCatalogue

open SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim ControlCatalogue

#print axioms SetTheory.BusyBeaver.ZFC.ControlCatalogue.leafEntries_length
#print axioms SetTheory.BusyBeaver.ZFC.ControlCatalogue.leafEntries_nodup
#print axioms SetTheory.BusyBeaver.ZFC.ControlCatalogue.leafEntries_sound
#print axioms SetTheory.BusyBeaver.ZFC.ControlCatalogue.entry_at_crank
#print axioms SetTheory.BusyBeaver.ZFC.ControlCatalogue.BT.get_ofList
#print axioms SetTheory.BusyBeaver.ZFC.ControlCatalogue.twalk_le

example (t : Tree) : (leafEntries t).length = SiteCoverage.leafCount t :=
  leafEntries_length t
example (t : Tree) : (leafEntries t).Nodup := leafEntries_nodup t
example (t : Tree) (P : List Bool) (e : Edge) (h : (P,e) ∈ leafEntries t) :
    SiteCoverage.LeafAt t P e := leafEntries_sound t P e h
example (t : Tree) (P : List Bool) (i : Nat) (e : Edge) (d : Nat)
    (h : twalk t P i = some (e,d)) :
    ∃ hr : crank (annotate t) P < (leafEntries t).length,
      (leafEntries t)[crank (annotate t) P] = (consume P (d-i), e) :=
  entry_at_crank t P i e d h
example {α : Type} (xs : List α) (n : Nat) : (BT.ofList xs).get n = xs[n]? :=
  BT.get_ofList xs n
example (t : Tree) (P : List Bool) (i : Nat) (e : Edge) (d : Nat)
    (h : twalk t P i = some (e,d)) : i ≤ d := twalk_le t P i e d h
