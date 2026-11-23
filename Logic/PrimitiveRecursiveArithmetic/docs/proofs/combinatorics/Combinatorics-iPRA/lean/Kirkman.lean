/- A closed finite certificate for Kirkman's schoolgirl problem.
    Checked with Lean 4.32.0, using kernel reduction.
    Labels 0,...,6 are A₀,...,A₆, 7,...,13 are B₀,...,B₆, and 14 is ∞. -/
import Init

namespace Kirkman

def baseDay : List (List Nat) :=
  [[14, 0, 7], [1, 2, 4], [3, 8, 12], [5, 11, 13], [6, 9, 10]]

def shiftLabel (d x : Nat) : Nat :=
  if x = 14 then 14 else (x / 7) * 7 + ((x % 7 + d) % 7)

def day (d : Nat) : List (List Nat) :=
  baseDay.map (List.map (shiftLabel d))

def week : List (List (List Nat)) := (List.range 7).map day

/-- Count individual occurrences, including repetitions within a row. -/
def occurrences (d x : Nat) : Nat := ((day d).flatten).count x

/-- Count rows in the entire week in which both labels occur. -/
def meetings (x y : Nat) : Nat :=
  (week.flatten.filter (fun row => row.contains x && row.contains y)).length

set_option maxRecDepth 16000
set_option maxHeartbeats 8000000

theorem shape : ∀ d : Fin 7, (day d).length = 5 ∧
    (day d).all (fun row => row.length == 3 && row.all (· < 15)) = true := by
  decide

theorem attendance : ∀ (d : Fin 7) (x : Fin 15), occurrences d x = 1 := by
  decide

theorem pairCoverage : ∀ x y : Fin 15, x < y → meetings x y = 1 := by
  decide

end Kirkman

#print axioms Kirkman.shape
#print axioms Kirkman.attendance
#print axioms Kirkman.pairCoverage
