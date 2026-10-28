import DiophantineConsistency.DirectScalarEnumerator

namespace EnumeratorCompatibilityProbe
open DiophantineConsistency
open SetTheory SetTheory.BusyBeaver.ZFC
open EnumPerm Code254 KCode222

private def oldStateEquiv : St ≃ ℕ × ℕ × ℕ × ℕ × ℕ × ℕ where
  toFun s := (s.pl, s.np, s.tw, s.ws, s.d, s.h)
  invFun s := ⟨s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, s.2.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
private instance : Primcodable St := Primcodable.ofEquiv _ oldStateEquiv
private instance : DecidableEq St := Encodable.decidableEqOfEncodable _

def oldRun (n : ℕ) (s : St) : Option St :=
  (fun o : Option St => o.bind enumStep)^[n] (some s)
def oldInitial : St := ⟨0, 4, 0, 0, 0, 0⟩
def oldHaltingTest (t : ℕ) : ℕ :=
  Encodable.encode (decide (oldRun t oldInitial = none))

example (n : ℕ) (s : St) : oldRun n s = boundedRun n s := rfl
example : oldInitial = initialState := rfl
example (n : ℕ) : oldHaltingTest n = haltingTest n := rfl
example (n : ℕ) : DirectEnumerator.program.val.eval n = haltingTest n :=
  DirectEnumerator.program.property n
example : REPred refutationInputs := refutationInputs_re
example : Nat.Primrec haltingTest := haltingTest_natPrimrec
example : Nat.Primrec' (fun v : List.Vector ℕ 1 => haltingTest v.head) :=
  haltingTest_vectorPrimrec
end EnumeratorCompatibilityProbe
