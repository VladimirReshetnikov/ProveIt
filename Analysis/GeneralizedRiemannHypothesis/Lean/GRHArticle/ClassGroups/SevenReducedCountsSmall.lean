import GRHArticle.ClassGroups.ReducedQuadraticForms

/-!
# Exact reduced-form counts for the small entries of the exponent-seven table
-/

namespace GRHArticle.ClassGroups


/-- Order discriminants with seven reduced representatives in the table. -/
def sevenReducedCountDiscriminants : List ℕ :=
  [71, 151, 223, 251, 284, 343, 463, 467, 487, 587, 604, 811, 827,
   859, 892, 1163, 1171, 1372, 1483, 1523, 1627, 1787, 1852, 1948, 1987, 2011,
   2083, 2179, 2251, 2467, 2707, 3019, 3067, 3187, 3907, 4603, 5107, 5923]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_71 : reducedQuadraticFormCount 71 = 7 := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_151 : reducedQuadraticFormCount 151 = 7 := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_223 : reducedQuadraticFormCount 223 = 7 := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_251 : reducedQuadraticFormCount 251 = 7 := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_284 : reducedQuadraticFormCount 284 = 7 := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_343 : reducedQuadraticFormCount 343 = 7 := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_463 : reducedQuadraticFormCount 463 = 7 := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_467 : reducedQuadraticFormCount 467 = 7 := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_487 : reducedQuadraticFormCount 487 = 7 := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_587 : reducedQuadraticFormCount 587 = 7 := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_604 : reducedQuadraticFormCount 604 = 7 := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_811 : reducedQuadraticFormCount 811 = 7 := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_827 : reducedQuadraticFormCount 827 = 7 := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_859 : reducedQuadraticFormCount 859 = 7 := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_892 : reducedQuadraticFormCount 892 = 7 := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_1163 : reducedQuadraticFormCount 1163 = 7 := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_1171 : reducedQuadraticFormCount 1171 = 7 := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_1372 : reducedQuadraticFormCount 1372 = 7 := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_1483 : reducedQuadraticFormCount 1483 = 7 := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_1523 : reducedQuadraticFormCount 1523 = 7 := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_1627 : reducedQuadraticFormCount 1627 = 7 := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_1787 : reducedQuadraticFormCount 1787 = 7 := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_1852 : reducedQuadraticFormCount 1852 = 7 := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_1948 : reducedQuadraticFormCount 1948 = 7 := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_1987 : reducedQuadraticFormCount 1987 = 7 := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_2011 : reducedQuadraticFormCount 2011 = 7 := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_2083 : reducedQuadraticFormCount 2083 = 7 := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_2179 : reducedQuadraticFormCount 2179 = 7 := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_2251 : reducedQuadraticFormCount 2251 = 7 := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_2467 : reducedQuadraticFormCount 2467 = 7 := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_2707 : reducedQuadraticFormCount 2707 = 7 := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_3019 : reducedQuadraticFormCount 3019 = 7 := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_3067 : reducedQuadraticFormCount 3067 = 7 := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_3187 : reducedQuadraticFormCount 3187 = 7 := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_3907 : reducedQuadraticFormCount 3907 = 7 := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_4603 : reducedQuadraticFormCount 4603 = 7 := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_5107 : reducedQuadraticFormCount 5107 = 7 := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_5923 : reducedQuadraticFormCount 5923 = 7 := by decide +kernel

theorem sevenReducedCountDiscriminants_count (d : ℕ) (hd : d ∈ sevenReducedCountDiscriminants) :
    reducedQuadraticFormCount d = 7 := by
  have hall : sevenReducedCountDiscriminants.all (fun n ↦ decide (reducedQuadraticFormCount n = 7)) = true := by
    simp only [sevenReducedCountDiscriminants, List.all_cons, List.all_nil,
      count_71, count_151, count_223, count_251, count_284, count_343, count_463,
      count_467, count_487, count_587, count_604, count_811, count_827, count_859,
      count_892, count_1163, count_1171, count_1372, count_1483, count_1523, count_1627,
      count_1787, count_1852, count_1948, count_1987, count_2011, count_2083, count_2179,
      count_2251, count_2467, count_2707, count_3019, count_3067, count_3187, count_3907,
      count_4603, count_5107, count_5923,
      decide_true, Bool.and_self]
  exact of_decide_eq_true (List.all_eq_true.mp hall d hd)

end GRHArticle.ClassGroups
