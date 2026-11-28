import GRHArticle.ClassGroups.ReducedQuadraticForms

/-!
# Exact reduced-form counts for the two large entries

Separate leading-coefficient intervals keep the kernel checks small.
-/

namespace GRHArticle.ClassGroups

private def checkedPartition (D : ℕ) (a : ℕ) : List (ℕ×ℕ) → Prop
  | [] => True
  | (len,n)::L => reducedQuadraticFormCountWindow D a len = n ∧ checkedPartition D (a+len) L

private theorem count_of_checkedPartition (D a : ℕ) (L : List (ℕ×ℕ))
    (h : checkedPartition D a L) :
    reducedQuadraticFormCountWindow D a (L.map Prod.fst).sum = (L.map Prod.snd).sum := by
  induction L generalizing a with
  | nil => simp [reducedQuadraticFormCountWindow, reducedQuadraticFormsWindow]
  | cons p L ih =>
    obtain ⟨len,n⟩ := p
    obtain ⟨hcur,htail⟩ := h
    simp only [List.map_cons, List.sum_cons]
    rw [reducedQuadraticFormCountWindow_append, hcur, ih _ htail]


set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_63499_1 : reducedQuadraticFormCountWindow 63499 1 10 = 3 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_63499_11 : reducedQuadraticFormCountWindow 63499 11 10 = 4 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_63499_21 : reducedQuadraticFormCountWindow 63499 21 10 = 4 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_63499_31 : reducedQuadraticFormCountWindow 63499 31 10 = 4 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_63499_41 : reducedQuadraticFormCountWindow 63499 41 10 = 2 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_63499_51 : reducedQuadraticFormCountWindow 63499 51 10 = 4 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_63499_61 : reducedQuadraticFormCountWindow 63499 61 10 = 2 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_63499_71 : reducedQuadraticFormCountWindow 63499 71 10 = 0 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_63499_81 : reducedQuadraticFormCountWindow 63499 81 10 = 6 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_63499_91 : reducedQuadraticFormCountWindow 63499 91 10 = 2 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_63499_101 : reducedQuadraticFormCountWindow 63499 101 10 = 6 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_63499_111 : reducedQuadraticFormCountWindow 63499 111 10 = 6 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_63499_121 : reducedQuadraticFormCountWindow 63499 121 10 = 4 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_63499_131 : reducedQuadraticFormCountWindow 63499 131 10 = 2 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_63499_141 : reducedQuadraticFormCountWindow 63499 141 5 = 0 := by
  decide +kernel

/-- The exact reduced-form count at discriminant `-63499`. -/
theorem reducedQuadraticFormCount_63499 : reducedQuadraticFormCount 63499 = 49 := by
  have hs : ((63499:ℕ)/3).sqrt = 145 := (Nat.eq_sqrt'.mpr (by decide :
    (145:ℕ)^2 ≤ 63499/3 ∧ 63499/3 < (145+1)^2)).symm
  rw [reducedQuadraticFormCount, hs]
  have h := count_of_checkedPartition 63499 1 [(10,3), (10,4), (10,4), (10,4), (10,2), (10,4), (10,2), (10,0), (10,6), (10,2), (10,6), (10,6), (10,4), (10,2), (5,0)]
    ⟨count_63499_1, count_63499_11, count_63499_21, count_63499_31, count_63499_41,
      count_63499_51, count_63499_61, count_63499_71, count_63499_81, count_63499_91,
      count_63499_101, count_63499_111, count_63499_121, count_63499_131, count_63499_141,
      trivial⟩
  change reducedQuadraticFormCountWindow 63499 1 145 = 49 at h
  exact h

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_118843_1 : reducedQuadraticFormCountWindow 118843 1 10 = 1 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_118843_11 : reducedQuadraticFormCountWindow 118843 11 10 = 6 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_118843_21 : reducedQuadraticFormCountWindow 118843 21 10 = 2 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_118843_31 : reducedQuadraticFormCountWindow 118843 31 10 = 2 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_118843_41 : reducedQuadraticFormCountWindow 118843 41 10 = 4 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_118843_51 : reducedQuadraticFormCountWindow 118843 51 10 = 2 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_118843_61 : reducedQuadraticFormCountWindow 118843 61 10 = 4 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_118843_71 : reducedQuadraticFormCountWindow 118843 71 10 = 4 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_118843_81 : reducedQuadraticFormCountWindow 118843 81 10 = 0 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_118843_91 : reducedQuadraticFormCountWindow 118843 91 10 = 2 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_118843_101 : reducedQuadraticFormCountWindow 118843 101 10 = 4 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_118843_111 : reducedQuadraticFormCountWindow 118843 111 10 = 0 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_118843_121 : reducedQuadraticFormCountWindow 118843 121 10 = 2 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_118843_131 : reducedQuadraticFormCountWindow 118843 131 10 = 4 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_118843_141 : reducedQuadraticFormCountWindow 118843 141 10 = 4 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_118843_151 : reducedQuadraticFormCountWindow 118843 151 10 = 2 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_118843_161 : reducedQuadraticFormCountWindow 118843 161 10 = 4 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_118843_171 : reducedQuadraticFormCountWindow 118843 171 10 = 0 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_118843_181 : reducedQuadraticFormCountWindow 118843 181 10 = 2 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem count_118843_191 : reducedQuadraticFormCountWindow 118843 191 9 = 0 := by
  decide +kernel

/-- The exact reduced-form count at discriminant `-118843`. -/
theorem reducedQuadraticFormCount_118843 : reducedQuadraticFormCount 118843 = 49 := by
  have hs : ((118843:ℕ)/3).sqrt = 199 := (Nat.eq_sqrt'.mpr (by decide :
    (199:ℕ)^2 ≤ 118843/3 ∧ 118843/3 < (199+1)^2)).symm
  rw [reducedQuadraticFormCount, hs]
  have h := count_of_checkedPartition 118843 1 [(10,1), (10,6), (10,2), (10,2), (10,4), (10,2), (10,4), (10,4), (10,0), (10,2), (10,4), (10,0), (10,2), (10,4), (10,4), (10,2), (10,4), (10,0), (10,2), (9,0)]
    ⟨count_118843_1, count_118843_11, count_118843_21, count_118843_31, count_118843_41,
      count_118843_51, count_118843_61, count_118843_71, count_118843_81, count_118843_91,
      count_118843_101, count_118843_111, count_118843_121, count_118843_131, count_118843_141,
      count_118843_151, count_118843_161, count_118843_171, count_118843_181, count_118843_191,
      trivial⟩
  change reducedQuadraticFormCountWindow 118843 1 199 = 49 at h
  exact h

end GRHArticle.ClassGroups
