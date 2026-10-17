import BusyBeaver.ZFC.FiniteControlTable254

set_option autoImplicit false
open SetTheory.BusyBeaver.ZFC
open RegisterPath RegisterPathClean RMBisim SiteCoverage FiniteControlTable254

#print axioms SetTheory.BusyBeaver.ZFC.FiniteControlTable254.leafEntries_length
#print axioms SetTheory.BusyBeaver.ZFC.FiniteControlTable254.leafEntries_sound
#print axioms SetTheory.BusyBeaver.ZFC.FiniteControlTable254.leafEntries_complete
#print axioms SetTheory.BusyBeaver.ZFC.FiniteControlTable254.leafEntries_nodup
#print axioms SetTheory.BusyBeaver.ZFC.FiniteControlTable254.actualEntries_length
#print axioms SetTheory.BusyBeaver.ZFC.FiniteControlTable254.source_accepted
#print axioms SetTheory.BusyBeaver.ZFC.FiniteControlTable254.source_walk
#print axioms SetTheory.BusyBeaver.ZFC.FiniteControlTable254.source_follow
#print axioms SetTheory.BusyBeaver.ZFC.FiniteControlTable254.source_injective
#print axioms SetTheory.BusyBeaver.ZFC.FiniteControlTable254.resolve_source
#print axioms SetTheory.BusyBeaver.ZFC.FiniteControlTable254.resolve_source_self
#print axioms SetTheory.BusyBeaver.ZFC.FiniteControlTable254.resolve_number_valid
#print axioms SetTheory.BusyBeaver.ZFC.FiniteControlTable254.first_source
#print axioms SetTheory.BusyBeaver.ZFC.FiniteControlTable254.empty_control

example (t : Tree) : (leafEntries t).length = leafCount t := leafEntries_length t
example (t : Tree) (P : List Bool) (e : Edge) (h : (P,e) ∈ leafEntries t) : LeafAt t P e :=
  leafEntries_sound t P e h
example {t : Tree} {P : List Bool} {e : Edge} (h : LeafAt t P e) : (P,e) ∈ leafEntries t :=
  leafEntries_complete h
example (t : Tree) : (leafEntries t).Nodup := leafEntries_nodup t
example : actualEntries.length = 6460 := actualEntries_length
example (i : Control) : SitePerm252.checkSite (source i).1 (source i).2 = true := source_accepted i
example (i : Control) :
    walk Prog254.program (Prog254.program.nnodes+1) Prog254.program.root (source i).1 0 =
      some ((source i).2,(source i).1.length) := source_walk i
example (i : Control) :
    follow Prog254.program (.node Prog254.program.root) (source i).1 = some (source i).2 := source_follow i
example (i j : Control) (h : source i = source j) : i = j := source_injective h
example (P : List Bool) (e : Edge) (d : Nat)
    (h : walk Prog254.program (Prog254.program.nnodes+1) Prog254.program.root P 0 = some (e,d)) :
    source (resolveControl P) = (consume P d,e) := resolve_source P e d h
example (i : Control) : resolveControl (source i).1 = i := resolve_source_self i
example (P : List Bool) : 0 < number (resolveControl P) ∧ number (resolveControl P) ≤ 6460 :=
  resolve_number_valid P
example : source ⟨0,by decide⟩ = ([false,false,false],.decnz 8) := first_source
example : resolveControl [] = ⟨0,by decide⟩ := empty_control
example (i : Control) : (source i).1.length ≤ 40 := source_length i
example (P : List Bool) : consume P P.length = P := consume_self P
example : leafEntries (.node (.leaf (.inc 0)) (.leaf .halt)) =
    [([false],.inc 0),([true],.halt)] := by rfl
