import Mertens

namespace Mertens

/-- Evaluate all prefix sums with one coefficient table. -/
def initialValues (n : Nat) : List Int :=
  let a := table n
  (List.range (n+1)).map (fun i => sum (fun k => (a[k]?).getD 0) i)

theorem initialValues_correct {i n : Nat} (h : i ≤ n) :
    (initialValues n)[i]? = some (M i) := by
  simp only [initialValues, List.getElem?_map, List.getElem?_range (show i < n+1 by omega),
    Option.map_some]
  change some (sum _ i) = some (M i)
  apply congrArg some
  apply sum_congr
  intro k _ hk
  exact table_stable (Nat.le_trans hk h)

/-- Entry 0 is M(0). Entries 1,...,143 give the published table. -/
def values143 : List Int := [
  0, 1, 0, -1, -1, -2, -1, -2, -2, -2, -1, -2,
  -2, -3, -2, -1, -1, -2, -2, -3, -3, -2, -1, -2,
  -2, -2, -1, -1, -1, -2, -3, -4, -4, -3, -2, -1,
  -1, -2, -1, 0, 0, -1, -2, -3, -3, -3, -2, -3,
  -3, -3, -3, -2, -2, -3, -3, -2, -2, -1, 0, -1,
  -1, -2, -1, -1, -1, 0, -1, -2, -2, -1, -2, -3,
  -3, -4, -3, -3, -3, -2, -3, -4, -4, -4, -3, -4,
  -4, -3, -2, -1, -1, -2, -2, -1, -1, 0, 1, 2,
  2, 1, 1, 1, 1, 0, -1, -2, -2, -3, -2, -3,
  -3, -4, -5, -4, -4, -5, -6, -5, -5, -5, -4, -3,
  -3, -3, -2, -1, -1, -1, -1, -2, -2, -1, -2, -3,
  -3, -2, -1, -1, -1, -2, -3, -4, -4, -3, -2, -1]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem computes143 : initialValues 143 = values143 := by decide +kernel

theorem lookup143 {i : Nat} (h : i ≤ 143) : values143[i]? = some (M i) := by
  rw [← computes143]
  exact initialValues_correct h

end Mertens
