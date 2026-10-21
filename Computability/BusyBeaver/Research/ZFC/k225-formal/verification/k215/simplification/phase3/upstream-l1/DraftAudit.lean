import BusyBeaver.ZFC.KEndpoint215
namespace SetTheory.BusyBeaver.ZFC.EnumPerm
open Code254 KCode222
def legacyExecAt (pl1 np1 : Nat) (s : St) : Option St :=
  match (unP pl1).1 with
  | 0 => if s.h = 1 then none
         else some ⟨(unP pl1).2, np1, s.tw, (unP s.ws).2, s.d, (unP s.ws).1⟩
  | 1 => some ⟨(unP pl1).2, np1, s.h, P s.tw s.ws, s.d, s.h⟩
  | 2 => some (if wim s.tw (s.d + (unP (unP pl1).2).1) = s.h
               then ⟨(unP (unP pl1).2).2, np1, s.d + (unP (unP pl1).2).1, P 0 s.ws,
                     s.d + (unP (unP pl1).2).1, 0⟩
               else ⟨(unP (unP pl1).2).2, np1, 0, s.ws, s.d + (unP (unP pl1).2).1, 0⟩)
  | c + 3 =>
      some ⟨(unP (unP (unP pl1).2).2).2, np1,
            gate (s.d + (unP (unP (unP pl1).2).2).1) (s.h + (unP (unP pl1).2).1) c,
            axStack (s.d + (unP (unP (unP pl1).2).2).1) s.h (s.h + (unP (unP pl1).2).1) c s.d
              s.tw s.ws, 0, 0⟩

theorem execAt_eq_legacy (pl1 np1 : Nat) (s : St) :
    execAt pl1 np1 s = legacyExecAt pl1 np1 s := by
  unfold execAt decode legacyExecAt
  generalize (unP pl1).1 = selector
  rcases selector with _ | _ | _ | c <;> simp only [cstep, toW]
  · by_cases h : s.h = 1 <;> simp only [h, if_true, if_false, Option.map]
  · rfl
  · by_cases h : wim s.tw (s.d + (unP (unP pl1).2).1) = s.h <;>
      simp only [h, if_true, if_false, Option.map]
  · rfl


theorem general_start (s : St) (hpl : s.pl = 0) (hs : Inv (toW s)) :
    HaltsFrom s ↔ C222 F := halts_iff hpl hs

theorem zero_start : HaltsFrom ⟨0, 0, 0, 0, 0, 0⟩ ↔ C222 F :=
  halts_iff rfl ⟨C222.truth, C222.truth, good_zero⟩

#print axioms execAt_eq_legacy
#print axioms general_start
#print axioms zero_start
end SetTheory.BusyBeaver.ZFC.EnumPerm
