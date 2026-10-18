import BusyBeaver.ZFC.ArithmeticControlSourceRank254
set_option autoImplicit false
open SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage FiniteControlTable254
open ArithmeticControlSourceRank254

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlSourceRank254.AtRank.bound
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlSourceRank254.AtRank.lookup
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlSourceRank254.source_of_atRank
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlSourceRank254.source_354
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlSourceRank254.source_6423

example {t : Tree} {i : Nat} {P : List Bool} {e : Edge}
    (h : AtRank t i P e) : i < leafCount t := h.bound
example {t : Tree} {i : Nat} {P : List Bool} {e : Edge}
    (h : AtRank t i P e) : (leafEntries t)[i]? = some (P, e) := h.lookup
example {q : Control} {P : List Bool} {e : Edge}
    (h : AtRank ActualTree254.tree q.val P e) : source q = (P, e) := source_of_atRank h
example : (source (⟨354, by decide⟩ : Control)).2 = .decnz 1 :=
  congrArg Prod.snd source_354
example : (source (⟨6423, by decide⟩ : Control)).2 = .decnz 6 :=
  congrArg Prod.snd source_6423
