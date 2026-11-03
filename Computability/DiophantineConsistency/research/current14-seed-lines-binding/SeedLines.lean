import DiophantineConsistency.DecimalMachine215

/-! Bind the twelve lists of decimal digits, including leading zeroes, to
`DecimalMachine215.seed`. This theorem interprets the explicit Lean digit lists;
a separate TeX extraction check relates them to the retained page. -/

namespace DiophantineConsistency.Current14SeedLines

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- Twelve consecutive chunks as typeset, read in source order. -/
def lines : List (List ℕ) := [
  [1, 2, 8, 8, 9, 2, 6, 0, 4, 1, 0, 3, 5, 9, 5, 6, 1, 7, 4, 6, 7, 3, 6, 5, 4, 0, 7, 4, 3, 5, 1, 5, 8, 4, 5, 1, 3, 4, 2, 4, 4, 2, 6, 0, 6, 4, 0, 0, 1, 2, 7, 0, 2, 0, 3, 3, 2, 1, 2, 6, 2, 1],
  [9, 5, 3, 9, 8, 0, 7, 4, 1, 8, 0, 7, 8, 4, 0, 5, 8, 5, 7, 1, 5, 1, 8, 4, 8, 8, 2, 8, 2, 1, 1, 9, 8, 6, 1, 0, 2, 3, 0, 9, 3, 3, 5, 5, 3, 8, 9, 4, 0, 6, 9, 3, 9, 4, 1, 4, 0, 4, 2, 8, 9, 2],
  [9, 7, 4, 5, 5, 7, 7, 3, 9, 9, 2, 1, 9, 3, 7, 8, 4, 7, 9, 5, 7, 0, 5, 0, 0, 1, 6, 1, 8, 7, 7, 7, 0, 2, 5, 9, 6, 6, 3, 6, 9, 1, 3, 7, 9, 5, 4, 8, 5, 9, 7, 6, 4, 5, 3, 2, 8, 3, 2, 7, 2, 2],
  [7, 5, 4, 1, 1, 8, 4, 3, 4, 1, 0, 8, 0, 9, 0, 3, 8, 7, 1, 3, 5, 0, 2, 6, 3, 3, 2, 0, 4, 6, 1, 7, 3, 3, 3, 2, 4, 6, 7, 3, 3, 6, 1, 6, 9, 4, 0, 9, 6, 4, 5, 7, 8, 2, 7, 2, 3, 6, 0, 9, 0, 1],
  [5, 6, 1, 8, 6, 2, 1, 6, 5, 0, 8, 5, 0, 4, 9, 5, 3, 6, 4, 9, 1, 9, 2, 7, 5, 2, 1, 5, 4, 5, 1, 9, 2, 6, 8, 0, 2, 4, 5, 0, 9, 9, 5, 2, 0, 8, 2, 9, 5, 0, 2, 3, 8, 8, 6, 5, 4, 6, 8, 3, 0, 7],
  [2, 2, 9, 9, 9, 6, 3, 2, 4, 8, 2, 7, 6, 9, 2, 5, 3, 9, 8, 0, 2, 7, 4, 0, 9, 1, 2, 1, 7, 4, 6, 0, 7, 0, 7, 8, 2, 9, 0, 2, 3, 9, 7, 0, 8, 1, 7, 2, 4, 4, 7, 9, 0, 3, 4, 0, 7, 0, 4, 4, 4, 9],
  [0, 9, 0, 8, 5, 5, 8, 1, 2, 7, 1, 1, 9, 2, 0, 7, 1, 6, 5, 6, 1, 7, 0, 7, 3, 2, 0, 0, 4, 9, 3, 7, 3, 3, 7, 0, 8, 2, 1, 7, 1, 1, 4, 1, 0, 8, 2, 4, 8, 6, 3, 8, 4, 2, 6, 9, 0, 7, 2, 8, 8, 4],
  [7, 2, 7, 7, 8, 0, 8, 7, 4, 1, 9, 6, 6, 3, 4, 1, 7, 9, 4, 2, 8, 9, 2, 5, 2, 0, 1, 7, 5, 6, 3, 0, 6, 4, 9, 7, 9, 2, 3, 2, 9, 2, 6, 5, 8, 3, 4, 4, 9, 0, 2, 5, 3, 0, 3, 5, 5, 7, 7, 5, 3, 3],
  [9, 6, 4, 4, 9, 6, 8, 9, 8, 0, 8, 3, 7, 5, 7, 8, 8, 4, 5, 7, 4, 8, 8, 9, 7, 1, 0, 1, 7, 0, 4, 3, 6, 8, 9, 8, 7, 5, 4, 3, 3, 1, 6, 2, 9, 7, 2, 3, 9, 0, 1, 7, 7, 9, 3, 6, 1, 2, 3, 0, 3, 2],
  [8, 9, 0, 2, 5, 6, 5, 7, 7, 5, 7, 4, 8, 9, 5, 2, 6, 3, 4, 2, 4, 9, 7, 4, 3, 8, 7, 7, 2, 0, 4, 5, 7, 1, 4, 0, 9, 9, 6, 6, 1, 5, 3, 2, 4, 8, 1, 1, 2, 3, 0, 5, 0, 2, 3, 5, 8, 9, 8, 9, 7, 3],
  [2, 7, 4, 4, 3, 6, 0, 9, 9, 0, 3, 8, 0, 0, 5, 4, 1, 1, 9, 9, 3, 5, 1, 4, 0, 5, 9, 8, 5, 7, 5, 4, 2, 7, 8, 3, 0, 7, 2, 2, 7, 7, 7, 7, 5, 8, 4, 4, 5, 4, 5, 0, 8, 4, 2, 2, 7, 1, 7, 9, 9, 8],
  [3, 3, 4, 1, 1, 3, 5, 6, 4, 4, 0, 9, 3, 3, 5, 3, 4, 6, 0, 7, 4, 8, 9, 2, 6, 8, 0, 3, 2, 8, 4, 3, 7]
]

/-- Reading each line in order preserves its leading zero digits. -/
def digits : List ℕ := lines.flatten

def decimalValue (ds : List ℕ) : ℕ := ds.foldl (fun acc d => 10 * acc + d) 0

/-- Every printed entry is a decimal digit, and the full decimal parse is the seed. -/
theorem decimal_lines_eq_seed :
    (∀ d ∈ digits, d < 10) ∧ digits.length = 715 ∧
      decimalValue digits = DecimalMachine215.seed := by
  decide +kernel

#print axioms decimal_lines_eq_seed

end DiophantineConsistency.Current14SeedLines
