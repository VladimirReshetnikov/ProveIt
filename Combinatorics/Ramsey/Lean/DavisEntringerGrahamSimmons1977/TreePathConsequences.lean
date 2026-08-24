import DavisEntringerGrahamSimmons1977.TreeConsequences

/-!
# Compositional certificates for the Davis insertion tree

The executable certificate in `TreeConsequences.lean` establishes that a
checked insertion path ends at a vertex of the Davis--Entringer--Graham--
Simmons tree.  This file strengthens that interface in three ways:

* paths and their Boolean certificates compose under list append;
* a checked path has the expected length and therefore lies in the exact
  computed tree level determined by its starting level and number of steps;
* every prefix of a checked path is itself certified at its exact level.

Thus a long certificate can be split into independently checked segments,
and one successful endpoint certificate simultaneously certifies its entire
ancestral chain.
-/

set_option autoImplicit false

namespace LeanProofs.DavisEntringerGrahamSimmons1977

/-- Executing two lists of insertion positions successively agrees with
executing their concatenation. -/
@[simp] theorem checkedTreePath_append (B : Block) (is js : List Nat) :
    checkedTreePath B (is ++ js) =
      checkedTreePath (checkedTreePath B is) js := by
  induction is generalizing B with
  | nil => simp [checkedTreePath]
  | cons i is ih =>
      simp only [List.cons_append, checkedTreePath]
      exact ih _

/-- Boolean insertion-path certificates compose under list append.  This is
the computational counterpart of `checkedTreePath_append`. -/
@[simp] theorem checkedTreePathCheck_append (B : Block) (is js : List Nat) :
    checkedTreePathCheck B (is ++ js) =
      (checkedTreePathCheck B is &&
        checkedTreePathCheck (checkedTreePath B is) js) := by
  induction is generalizing B with
  | nil => simp [checkedTreePathCheck, checkedTreePath]
  | cons i is ih =>
      simp only [List.cons_append, checkedTreePathCheck, checkedTreePath]
      rw [ih]
      simp only [Bool.and_assoc]

/-- A concatenated path certificate succeeds exactly when its first segment
and the translated second segment both succeed. -/
theorem checkedTreePathCheck_append_eq_true_iff (B : Block) (is js : List Nat) :
    checkedTreePathCheck B (is ++ js) = true ↔
      checkedTreePathCheck B is = true ∧
        checkedTreePathCheck (checkedTreePath B is) js = true := by
  simp

/-- Success of a path certificate is inherited by every prefix. -/
theorem checkedTreePathCheck_take_eq_true {B : Block} {is : List Nat}
    (hcheck : checkedTreePathCheck B is = true) (n : Nat) :
    checkedTreePathCheck B (is.take n) = true := by
  rw [← List.take_append_drop n is] at hcheck
  exact (checkedTreePathCheck_append_eq_true_iff
    B (is.take n) (is.drop n)).mp hcheck |>.1

/-- Every successful insertion in a checked path increases the block length
by one, so the endpoint length is determined solely by the path length. -/
theorem checkedTreePath_length_of_check {B : Block} {is : List Nat}
    (hcheck : checkedTreePathCheck B is = true) :
    (checkedTreePath B is).length = B.length + is.length := by
  induction is generalizing B with
  | nil => simp [checkedTreePath]
  | cons i is ih =>
      simp only [checkedTreePathCheck, Bool.and_eq_true, decide_eq_true_eq,
        blockMidpointFreeCheck_eq_true] at hcheck
      rcases hcheck with ⟨⟨⟨hi, _⟩, _⟩, htail⟩
      let B' := B.insertIdx i (B.length + 1)
      have hB' : B'.length = B.length + 1 := by
        simpa [B'] using List.length_insertIdx_of_le_length hi (B.length + 1)
      change (checkedTreePath B' is).length = B.length + (is.length + 1)
      rw [ih htail, hB']
      omega

/-- A checked path from level `k` lands in level `k + is.length`.  This
strengthens endpoint soundness by also recovering the exact executable level. -/
theorem checkedTreePath_mem_computedLevel {B : Block} {is : List Nat} {k : Nat}
    (htree : IsTreeVertex B) (hlength : B.length = 3 + k)
    (hcheck : checkedTreePathCheck B is = true) :
    checkedTreePath B is ∈ computedTreeLevel (k + is.length) := by
  apply treeVertex_mem_computedLevel_of_length
    (checkedTreePathCheck_sound htree hcheck)
  have hend := checkedTreePath_length_of_check hcheck
  omega

/-- Every prefix of one successful certificate is a tree vertex. -/
theorem checkedTreePath_take_isTreeVertex {B : Block} {is : List Nat}
    (htree : IsTreeVertex B) (hcheck : checkedTreePathCheck B is = true)
    (n : Nat) :
    IsTreeVertex (checkedTreePath B (is.take n)) := by
  exact checkedTreePathCheck_sound htree
    (checkedTreePathCheck_take_eq_true hcheck n)

/-- Every prefix of a successful certificate lies in its exact computed tree
level.  The bound `n ≤ is.length` lets the level be stated as `k + n` rather
than using `length (take n is)`. -/
theorem checkedTreePath_take_mem_computedLevel {B : Block} {is : List Nat}
    {k n : Nat} (htree : IsTreeVertex B) (hlength : B.length = 3 + k)
    (hcheck : checkedTreePathCheck B is = true) (hn : n ≤ is.length) :
    checkedTreePath B (is.take n) ∈ computedTreeLevel (k + n) := by
  have hprefix := checkedTreePathCheck_take_eq_true hcheck n
  have hmem := checkedTreePath_mem_computedLevel htree hlength hprefix
  simpa [List.length_take, Nat.min_eq_left hn] using hmem

/-- The published maximum-length witness certificate also certifies every
one of its first `n` ancestors at executable level `n`. -/
theorem maximumTreeWitness_prefix_mem_computedLevel {n : Nat}
    (hn : n ≤ maximumTreeInsertionPositions.length) :
    checkedTreePath [1, 3, 2] (maximumTreeInsertionPositions.take n) ∈
      computedTreeLevel n := by
  simpa using checkedTreePath_take_mem_computedLevel
    (B := [1, 3, 2]) (is := maximumTreeInsertionPositions) (k := 0) (n := n)
    IsTreeVertex.root132 (by norm_num) maximumTreeWitness_certificate hn

end LeanProofs.DavisEntringerGrahamSimmons1977
