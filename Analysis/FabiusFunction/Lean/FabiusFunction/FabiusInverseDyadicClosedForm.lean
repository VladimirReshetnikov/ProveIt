import FabiusFunction.FabiusRecurrenceSequence
import FabiusFunction.FabiusInverse
import Mathlib.Combinatorics.Enumerative.Composition

/-!
# Nonrecursive inverse-dyadic Fabius values

This module solves the triangular recurrence for `F(2⁻ⁿ)` by summing the
weights of all increasing paths from `0` to `n`. Such paths are encoded by
ordered compositions of `n`. The resulting formula is finite and
nonrecursive; at `n = 0`, the unique empty composition contributes `1`.

The generic path layer separates multiplicative path weights from
semiring-valued path sums, proves both last-edge and edge-count
decompositions, and solves arbitrary triangular recurrences. The Fabius
specialization then identifies the exact rational composition sum with
`fabiusAtInverseTwoPow`, and supplies bounded and signed-global real
corollaries for every model satisfying the Fabius equations.  The final
inverse corollaries state directly that these explicit finite sums are sent
back to `2⁻ⁿ` by the totalized inverse Fabius function.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset

namespace Fabius

noncomputable section

namespace Composition

/-! ## Compositions and their last block -/

/-- Delete the last block of a composition. -/
def dropLast {n : ℕ} (c : Composition n) : Composition c.blocks.dropLast.sum where
  blocks := c.blocks.dropLast
  blocks_pos := fun hi => c.blocks_pos (c.blocks.dropLast_subset hi)
  blocks_sum := rfl

/-- Split a nonempty composition immediately before its last block. -/
def splitLast {n : ℕ} (hn : 0 < n) (c : Composition n) :
    Σ k : Fin n, Composition k := by
  have hc : c.blocks ≠ [] := by
    intro h
    have : n = 0 := c.blocks_eq_nil.mp h
    omega
  let d := c.blocks.getLast hc
  have hdmem : d ∈ c.blocks := List.getLast_mem hc
  have hd : 0 < d := c.blocks_pos hdmem
  have hsum : c.blocks.dropLast.sum + d = n := by
    calc
      c.blocks.dropLast.sum + d =
          (c.blocks.dropLast ++ [c.blocks.getLast hc]).sum := by simp [d]
      _ = c.blocks.sum := congrArg List.sum (c.blocks.dropLast_append_getLast hc)
      _ = n := c.blocks_sum
  exact ⟨⟨c.blocks.dropLast.sum, by omega⟩, Composition.dropLast c⟩

/-- Append the last block encoded by a proper prefix endpoint. -/
def joinLast {n : ℕ} (s : Σ k : Fin n, Composition k) : Composition n := by
  rcases s with ⟨k, c⟩
  have hkn : k.val ≤ n := k.isLt.le
  have hd : 0 < n - k.val := Nat.sub_pos_of_lt k.isLt
  exact {
    blocks := c.blocks ++ [n - k.val]
    blocks_pos := by
      intro i hi
      simp only [List.mem_append, List.mem_singleton] at hi
      exact hi.elim c.blocks_pos (fun h => h ▸ hd)
    blocks_sum := by simp [Nat.add_sub_of_le hkn]
  }

/-- A composition of a positive integer is equivalently a proper prefix endpoint
together with a composition ending at that endpoint. -/
def splitLastEquiv (n : ℕ) (hn : 0 < n) :
    Composition n ≃ Σ k : Fin n, Composition k where
  toFun := splitLast hn
  invFun := joinLast
  left_inv := by
    intro c
    have hc : c.blocks ≠ [] := by
      intro h
      have : n = 0 := c.blocks_eq_nil.mp h
      omega
    have hd : 0 < c.blocks.getLast hc :=
      c.blocks_pos (List.getLast_mem hc)
    have hsum : c.blocks.dropLast.sum + c.blocks.getLast hc = n := by
      calc
        c.blocks.dropLast.sum + c.blocks.getLast hc =
            (c.blocks.dropLast ++ [c.blocks.getLast hc]).sum := by simp
        _ = c.blocks.sum := congrArg List.sum (c.blocks.dropLast_append_getLast hc)
        _ = n := c.blocks_sum
    have hlast : n - c.blocks.dropLast.sum = c.blocks.getLast hc := by omega
    apply Composition.ext
    simp only [joinLast, splitLast, dropLast]
    rw [hlast]
    exact c.blocks.dropLast_append_getLast hc
  right_inv := by
    rintro ⟨k, c⟩
    have hk : (splitLast hn (joinLast ⟨k, c⟩)).1 = k := by
      apply Fin.ext
      simp [splitLast, joinLast]
    rw [Sigma.ext_iff]
    refine ⟨hk, ?_⟩
    let p := (splitLast hn (joinLast ⟨k, c⟩)).2
    have hnat : (splitLast hn (joinLast ⟨k, c⟩)).1.val = k.val :=
      congrArg Fin.val hk
    have hcast : p.cast hnat = c := by
      apply Composition.ext
      simp [p, splitLast, joinLast, dropLast]
    exact (Composition.cast_heq p hnat).symm.trans (heq_of_eq hcast)

/-! ## Multiplicative path weights -/

section PathWeights

variable {R : Type*} [Monoid R]

/-- The product of edge weights along a list of positive increments, starting
at `i`. -/
def pathWeightFrom (w : ℕ → ℕ → R) : ℕ → List ℕ → R
  | _, [] => 1
  | i, d :: ds => w i (i + d) * pathWeightFrom w (i + d) ds

/-- The empty increment list contributes the empty product `1`, from any
starting index. -/
@[simp]
theorem pathWeightFrom_nil (w : ℕ → ℕ → R) (i : ℕ) :
    pathWeightFrom w i [] = 1 := rfl

/-- Peeling the first increment: the edge from `i` to `i + d`, times the
weight of the remaining path started at `i + d`. -/
@[simp]
theorem pathWeightFrom_cons (w : ℕ → ℕ → R)
    (i d : ℕ) (ds : List ℕ) :
    pathWeightFrom w i (d :: ds) =
      w i (i + d) * pathWeightFrom w (i + d) ds := rfl

/-- Path weights are multiplicative under concatenation of increment lists:
the second factor starts at `i` shifted by the sum of the first list.  Used
by `pathWeight_append_single` and by the last-edge decomposition
`pathSum_eq_sum_range`. -/
theorem pathWeightFrom_append (w : ℕ → ℕ → R)
    (i : ℕ) (xs ys : List ℕ) :
    pathWeightFrom w i (xs ++ ys) =
      pathWeightFrom w i xs * pathWeightFrom w (i + xs.sum) ys := by
  induction xs generalizing i with
  | nil => simp
  | cons d ds ih =>
      simp only [List.cons_append, pathWeightFrom_cons, List.sum_cons]
      rw [ih]
      simp only [mul_assoc, Nat.add_assoc]

/-- The product of the weights of all successive edges of a composition. -/
def pathWeight {n : ℕ} (w : ℕ → ℕ → R) (c : Composition n) : R :=
  pathWeightFrom w 0 c.blocks

/-- The composition `Composition.ones 0` is the empty path, so its weight is
the empty product `1`. -/
@[simp]
theorem pathWeight_ones_zero (w : ℕ → ℕ → R) :
    pathWeight w (Composition.ones 0) = 1 := rfl

/-- Appending a final block of positive size `d` to a composition of `m`
multiplies the path weight by the single edge weight `w m (m + d)`. -/
@[simp]
theorem pathWeight_append_single {m d : ℕ} (hd : 0 < d)
    (w : ℕ → ℕ → R) (c : Composition m) :
    pathWeight w (c.append (Composition.single d hd)) =
      pathWeight w c * w m (m + d) := by
  rw [pathWeight, pathWeight, Composition.append_blocks,
    pathWeightFrom_append]
  simp [c.blocks_sum]

end PathWeights

/-! ## Semiring-valued path sums -/

section PathSums

variable {R : Type*} [Semiring R]

/-- Sum of the weights of all increasing paths from `0` to `n`, encoded by
the positive increments of a composition of `n`. -/
def pathSum (w : ℕ → ℕ → R) (n : ℕ) : R :=
  ∑ c : Composition n, pathWeight w c

/-- The path sum at `0` is `1`: the only composition of `0` is the empty
path, of weight `1`. -/
@[simp]
theorem pathSum_zero (w : ℕ → ℕ → R) : pathSum w 0 = 1 := by
  rw [pathSum]
  have h : ∀ c : Composition 0, c = Composition.ones 0 := by
    intro c
    apply Composition.ext
    exact c.blocks_eq_nil.mpr rfl
  letI : Unique (Composition 0) :=
    { default := Composition.ones 0
      uniq := h }
  rw [Fintype.sum_unique]
  exact pathWeight_ones_zero w

/-- Last-edge decomposition of the weighted path sum. -/
theorem pathSum_eq_sum_range (w : ℕ → ℕ → R)
    (n : ℕ) (hn : 0 < n) :
    pathSum w n = ∑ k ∈ range n, pathSum w k * w k n := by
  rw [pathSum]
  calc
    (∑ c : Composition n, pathWeight w c) =
        ∑ s : Σ k : Fin n, Composition k,
          pathWeight w ((splitLastEquiv n hn).symm s) := by
            exact Fintype.sum_equiv (splitLastEquiv n hn) _ _ (fun c => by simp)
    _ = ∑ k : Fin n, ∑ c : Composition k,
          pathWeight w c * w k n := by
            rw [Fintype.sum_sigma]
            apply Finset.sum_congr rfl
            intro k _hk
            apply Finset.sum_congr rfl
            intro c _hc
            simp [splitLastEquiv, joinLast, pathWeight,
              pathWeightFrom_append, c.blocks_sum, Nat.add_sub_of_le k.isLt.le]
    _ = ∑ k : Fin n, pathSum w k * w k n := by
            apply Finset.sum_congr rfl
            intro k _hk
            rw [pathSum, Finset.sum_mul]
    _ = ∑ k ∈ range n, pathSum w k * w k n := by
            exact Fin.sum_univ_eq_sum_range
              (fun k => pathSum w k * w k n) n

/-- The contribution of paths having exactly `r` edges. -/
def pathSumOfLength (w : ℕ → ℕ → R) (n r : ℕ) : R :=
  ∑ c : Composition n, if c.length = r then pathWeight w c else 0

/-- Partition all paths from `0` to `n` by their number of edges. This
uniform form includes `n = 0`, where the empty path has length zero. -/
theorem pathSum_eq_sum_length_range (w : ℕ → ℕ → R) (n : ℕ) :
    pathSum w n =
      ∑ r ∈ range (n + 1), pathSumOfLength w n r := by
  change (∑ c : Composition n, pathWeight w c) =
    ∑ r ∈ range (n + 1),
      ∑ c : Composition n,
        if c.length = r then pathWeight w c else 0
  calc
    (∑ c : Composition n, pathWeight w c) =
        ∑ c : Composition n, ∑ r ∈ range (n + 1),
          if c.length = r then pathWeight w c else 0 := by
            apply Finset.sum_congr rfl
            intro c _hc
            have hlen : c.length ∈ range (n + 1) := by
              exact mem_range.mpr (Nat.lt_succ_of_le c.length_le)
            simp [hlen]
    _ = ∑ r ∈ range (n + 1), ∑ c : Composition n,
          if c.length = r then pathWeight w c else 0 := by
            exact Finset.sum_comm

/-- Partition the paths from `0` to a positive endpoint according to their
number of edges. -/
theorem pathSum_eq_sum_length (w : ℕ → ℕ → R)
    (n : ℕ) (hn : 0 < n) :
    pathSum w n = ∑ r ∈ Icc 1 n, pathSumOfLength w n r := by
  change (∑ c : Composition n, pathWeight w c) =
    ∑ r ∈ Icc 1 n,
      ∑ c : Composition n,
        if c.length = r then pathWeight w c else 0
  calc
    (∑ c : Composition n, pathWeight w c) =
        ∑ c : Composition n, ∑ r ∈ Icc 1 n,
          if c.length = r then pathWeight w c else 0 := by
            apply Finset.sum_congr rfl
            intro c _hc
            have hlen : c.length ∈ Icc 1 n := by
              exact mem_Icc.mpr ⟨c.length_pos_of_pos hn, c.length_le⟩
            simp [hlen]
    _ = ∑ r ∈ Icc 1 n, ∑ c : Composition n,
          if c.length = r then pathWeight w c else 0 := by
            exact Finset.sum_comm

end PathSums

end Composition

namespace Composition

variable {R : Type*} [CommMonoid R]

private theorem pathWeightFrom_eq_prod_aux
    (w : ℕ → ℕ → R) (i : ℕ) (xs : List ℕ) :
    pathWeightFrom w i xs =
      ∏ j : Fin xs.length,
        w (i + (xs.take j).sum)
          (i + (xs.take ((j : ℕ) + 1)).sum) := by
  induction xs generalizing i with
  | nil => simp
  | cons d ds ih =>
      rw [pathWeightFrom_cons]
      simp only [List.length_cons]
      rw [Fin.prod_univ_succ]
      simp only [Fin.val_zero, List.take_zero, List.sum_nil, add_zero,
        List.take_succ_cons, List.sum_cons]
      rw [ih]
      apply congrArg (fun z => w i (i + d) * z)
      apply Finset.prod_congr rfl
      intro j _hj
      simp only [Fin.val_succ, List.take_succ_cons, List.sum_cons]
      simp only [Nat.add_assoc]

/-- The chronological product interpretation of `pathWeight`: the `j`-th
factor is the edge between two consecutive partial sums of the blocks. -/
theorem pathWeight_eq_boundary_product
    (w : ℕ → ℕ → R) {n : ℕ} (c : Composition n) :
    pathWeight w c =
      ∏ j : Fin c.length,
        w (c.sizeUpTo j) (c.sizeUpTo ((j : ℕ) + 1)) := by
  simpa only [pathWeight, Composition.sizeUpTo, zero_add] using
    pathWeightFrom_eq_prod_aux w 0 c.blocks

end Composition

section TriangularRecurrence

variable {R : Type*} [Semiring R]

/-- A triangular recurrence is solved by the sum of the weights of all paths
from its initial index. -/
theorem triangularRecurrence_eq_initial_mul_pathSum
    (x : ℕ → R) (w : ℕ → ℕ → R) (b : R)
    (hzero : x 0 = b)
    (hrec : ∀ n, 0 < n →
      x n = ∑ k ∈ range n, x k * w k n) (n : ℕ) :
    x n = b * Composition.pathSum w n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => simp [hzero]
      | succ n =>
          have hn : 0 < n + 1 := by omega
          rw [hrec (n + 1) hn,
            Composition.pathSum_eq_sum_range w (n + 1) hn]
          calc
            (∑ k ∈ range (n + 1), x k * w k (n + 1)) =
                ∑ k ∈ range (n + 1),
                  (b * Composition.pathSum w k) * w k (n + 1) := by
                    apply Finset.sum_congr rfl
                    intro k hk
                    rw [ih k (mem_range.mp hk)]
            _ = b * ∑ k ∈ range (n + 1),
                  Composition.pathSum w k * w k (n + 1) := by
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro k _hk
                    simp only [mul_assoc]

/-- Consequently, a triangular recurrence with prescribed initial value has
at most one solution. -/
theorem triangularRecurrence_unique
    (x y : ℕ → R) (w : ℕ → ℕ → R)
    (hzero : x 0 = y 0)
    (hx : ∀ n, 0 < n →
      x n = ∑ k ∈ range n, x k * w k n)
    (hy : ∀ n, 0 < n →
      y n = ∑ k ∈ range n, y k * w k n) :
    x = y := by
  funext n
  rw [triangularRecurrence_eq_initial_mul_pathSum x w (x 0) rfl hx n,
    triangularRecurrence_eq_initial_mul_pathSum y w (y 0) rfl hy n,
    hzero]

end TriangularRecurrence

/-! ### The Fabius recurrence -/

/-- Weight of the edge `k → n` in the elementary Fabius recurrence. -/
def fabiusRecurrenceEdge (k n : ℕ) : ℚ :=
  (((2 : ℚ) ^ n - 1) * (((n - k + 1).factorial : ℕ) : ℚ))⁻¹

/-- For `n ≥ 1`, the Fabius recurrence in last-edge form: `a n` is the sum
over `k < n` of `a k` times the edge weight `fabiusRecurrenceEdge k n`.  This
repackages `fabiusRecurrenceSequence_recurrence`, and is the hypothesis fed
to the triangular solver in `fabiusRecurrenceSequence_eq_pathSum`. -/
theorem fabiusRecurrenceSequence_edge_recurrence (n : ℕ) (hn : 0 < n) :
    fabiusRecurrenceSequence n =
      ∑ k ∈ range n,
        fabiusRecurrenceSequence k * fabiusRecurrenceEdge k n := by
  rw [fabiusRecurrenceSequence_recurrence n hn]
  rw [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _hk
  simp only [fabiusRecurrenceEdge, div_eq_mul_inv, mul_inv_rev]
  ring

/-- Nonrecursive path expansion of the sequence in the Fabius recurrence. -/
theorem fabiusRecurrenceSequence_eq_pathSum (n : ℕ) :
    fabiusRecurrenceSequence n =
      Composition.pathSum fabiusRecurrenceEdge n := by
  simpa using triangularRecurrence_eq_initial_mul_pathSum
    fabiusRecurrenceSequence fabiusRecurrenceEdge 1
      fabiusRecurrenceSequence_zero
      fabiusRecurrenceSequence_edge_recurrence n

/-- Exact rational Fabius value as a finite nonrecursive sum over all chains
from `0` to `n`. -/
theorem fabiusAtInverseTwoPow_eq_pathSum (n : ℕ) :
    fabiusAtInverseTwoPow n =
      ((2 : ℚ) ^ n.choose 2)⁻¹ *
        Composition.pathSum fabiusRecurrenceEdge n := by
  rw [fabiusAtInverseTwoPow_eq_recurrenceSequence,
    fabiusRecurrenceSequence_eq_pathSum]

/-- The article's chronological composition weight. If the blocks of `c` are
`r₁, ..., rₘ` and `sⱼ = r₁ + ⋯ + rⱼ`, this is
`∏ j, ((2^sⱼ - 1) * (rⱼ + 1)!)⁻¹`. -/
def fabiusCompositionWeight {n : ℕ} (c : Composition n) : ℚ :=
  ∏ j : Fin c.length,
    (((2 : ℚ) ^ c.sizeUpTo ((j : ℕ) + 1) - 1) *
      (((c.blocksFun j + 1).factorial : ℕ) : ℚ))⁻¹

/-- The finite sum of the article's weights over all ordered compositions of
`n`. For `n = 0`, the unique empty composition contributes the empty product
`1`. -/
def fabiusCompositionSum (n : ℕ) : ℚ :=
  ∑ c : Composition n, fabiusCompositionWeight c

/-- Along any composition, the generic path weight of `fabiusRecurrenceEdge`
is the article's chronological weight `fabiusCompositionWeight`.  This is the
bridge used by `fabiusCompositionSum_eq_pathSum` and by the two expanded
edge-count formulas at the end of this file. -/
theorem Composition.pathWeight_fabiusRecurrenceEdge
    {n : ℕ} (c : Composition n) :
    pathWeight fabiusRecurrenceEdge c = fabiusCompositionWeight c := by
  rw [pathWeight_eq_boundary_product, fabiusCompositionWeight]
  apply Finset.prod_congr rfl
  intro j _hj
  rw [c.sizeUpTo_succ' j]
  simp [fabiusRecurrenceEdge]

/-- The generic path sum and the explicit chronological composition sum are
the same finite object. -/
theorem fabiusCompositionSum_eq_pathSum (n : ℕ) :
    fabiusCompositionSum n =
      Composition.pathSum fabiusRecurrenceEdge n := by
  rw [fabiusCompositionSum, Composition.pathSum]
  apply Finset.sum_congr rfl
  intro c _hc
  exact (Composition.pathWeight_fabiusRecurrenceEdge c).symm

/-- The normalized recurrence sequence is the explicit sum over ordered
compositions. -/
theorem fabiusRecurrenceSequence_eq_sum_compositions (n : ℕ) :
    fabiusRecurrenceSequence n = fabiusCompositionSum n := by
  rw [fabiusRecurrenceSequence_eq_pathSum,
    fabiusCompositionSum_eq_pathSum]

/-- The explicit composition sum satisfies the same last-edge recurrence as
the normalized Fabius sequence. -/
theorem fabiusCompositionSum_recurrence (n : ℕ) (hn : 0 < n) :
    fabiusCompositionSum n =
      ∑ k ∈ range n,
        fabiusCompositionSum k * fabiusRecurrenceEdge k n := by
  calc
    fabiusCompositionSum n =
        Composition.pathSum fabiusRecurrenceEdge n :=
      fabiusCompositionSum_eq_pathSum n
    _ = ∑ k ∈ range n,
          Composition.pathSum fabiusRecurrenceEdge k *
            fabiusRecurrenceEdge k n :=
      Composition.pathSum_eq_sum_range fabiusRecurrenceEdge n hn
    _ = ∑ k ∈ range n,
          fabiusCompositionSum k * fabiusRecurrenceEdge k n := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [fabiusCompositionSum_eq_pathSum]

/-- The composition sum at `0` is `1`: the only composition of `0` is the
empty one, whose weight is the empty product. -/
@[simp]
theorem fabiusCompositionSum_zero : fabiusCompositionSum 0 = 1 := by
  rw [← fabiusRecurrenceSequence_eq_sum_compositions,
    fabiusRecurrenceSequence_zero]

/-- Every explicit composition sum is strictly positive. -/
theorem fabiusCompositionSum_pos (n : ℕ) :
    0 < fabiusCompositionSum n := by
  rw [← fabiusRecurrenceSequence_eq_sum_compositions]
  exact fabiusRecurrenceSequence_pos n

/-- Exact rational nonrecursive composition formula for `F(2⁻ⁿ)`. -/
theorem fabiusAtInverseTwoPow_eq_sum_compositions (n : ℕ) :
    fabiusAtInverseTwoPow n =
      ((2 : ℚ) ^ n.choose 2)⁻¹ * fabiusCompositionSum n := by
  rw [fabiusAtInverseTwoPow_eq_recurrenceSequence,
    fabiusRecurrenceSequence_eq_sum_compositions]

/-- Fully expanded version of the nonrecursive composition formula, with the
outer triangular power written as a literal negative exponent. -/
theorem fabiusAtInverseTwoPow_eq_composition_formula (n : ℕ) :
    fabiusAtInverseTwoPow n =
      (2 : ℚ) ^ (-(n.choose 2 : ℤ)) *
        ∑ c : Composition n,
          ∏ j : Fin c.length,
            (((2 : ℚ) ^ c.sizeUpTo ((j : ℕ) + 1) - 1) *
              (((c.blocksFun j + 1).factorial : ℕ) : ℚ))⁻¹ := by
  simpa [fabiusCompositionSum, fabiusCompositionWeight, zpow_neg] using
    fabiusAtInverseTwoPow_eq_sum_compositions n

/-- Uniform edge-count form of the inverse-dyadic formula. Unlike the
article-style positive-index form below, this also covers `n = 0`; the sole
length-zero path is the empty composition. -/
theorem fabiusAtInverseTwoPow_eq_sum_path_lengths_range (n : ℕ) :
    fabiusAtInverseTwoPow n =
      ((2 : ℚ) ^ n.choose 2)⁻¹ *
        ∑ r ∈ range (n + 1),
          Composition.pathSumOfLength fabiusRecurrenceEdge n r := by
  rw [fabiusAtInverseTwoPow_eq_pathSum,
    Composition.pathSum_eq_sum_length_range]

/-- Source-facing form: first sum over the number `r` of strict steps, then
over compositions with exactly `r` blocks. -/
theorem fabiusAtInverseTwoPow_eq_sum_path_lengths
    (n : ℕ) (hn : 0 < n) :
    fabiusAtInverseTwoPow n =
      ((2 : ℚ) ^ n.choose 2)⁻¹ *
        ∑ r ∈ Icc 1 n,
          Composition.pathSumOfLength fabiusRecurrenceEdge n r := by
  rw [fabiusAtInverseTwoPow_eq_pathSum,
    Composition.pathSum_eq_sum_length fabiusRecurrenceEdge n hn]

/-- Source-facing multiple-sum form: first sum over the number of blocks,
then over all compositions with that many blocks. -/
theorem fabiusAtInverseTwoPow_eq_composition_formula_by_length
    (n : ℕ) (hn : 0 < n) :
    fabiusAtInverseTwoPow n =
      (2 : ℚ) ^ (-(n.choose 2 : ℤ)) *
        ∑ r ∈ Icc 1 n,
          ∑ c : Composition n,
            if c.length = r then
              ∏ j : Fin c.length,
                (((2 : ℚ) ^ c.sizeUpTo ((j : ℕ) + 1) - 1) *
                  (((c.blocksFun j + 1).factorial : ℕ) : ℚ))⁻¹
            else 0 := by
  rw [fabiusAtInverseTwoPow_eq_sum_path_lengths n hn]
  simp only [Composition.pathSumOfLength,
    Composition.pathWeight_fabiusRecurrenceEdge, fabiusCompositionWeight,
    zpow_neg, zpow_natCast]

/-- Fully expanded edge-count formula valid uniformly for every `n`, with
the length-zero contribution retained when `n = 0`. -/
theorem fabiusAtInverseTwoPow_eq_composition_formula_by_length_range (n : ℕ) :
    fabiusAtInverseTwoPow n =
      (2 : ℚ) ^ (-(n.choose 2 : ℤ)) *
        ∑ r ∈ range (n + 1),
          ∑ c : Composition n,
            if c.length = r then
              ∏ j : Fin c.length,
                (((2 : ℚ) ^ c.sizeUpTo ((j : ℕ) + 1) - 1) *
                  (((c.blocksFun j + 1).factorial : ℕ) : ℚ))⁻¹
            else 0 := by
  rw [fabiusAtInverseTwoPow_eq_sum_path_lengths_range]
  simp only [Composition.pathSumOfLength,
    Composition.pathWeight_fabiusRecurrenceEdge, fabiusCompositionWeight,
    zpow_neg, zpow_natCast]

/-- Real analytic version for any bounded Fabius function satisfying its
defining equations. -/
theorem fabiusFunction_inverse_two_pow_eq_sum_compositions
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    fabiusReal F (((2 : ℝ) ^ n)⁻¹) =
      ((2 : ℝ) ^ n.choose 2)⁻¹ * (fabiusCompositionSum n : ℝ) := by
  rw [fabius_inverse_two_pow_eq_recurrenceSequence F hF n,
    fabiusRecurrenceSequence_eq_sum_compositions]

/-- The totalized inverse sends the explicit real composition formula back
to `2⁻ⁿ`.  This is uniform in the bounded Fabius model and includes `n = 0`. -/
theorem fabiusInv_two_pow_choose_mul_fabiusCompositionSum
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    fabiusInv F hF
        (((2 : ℝ) ^ n.choose 2)⁻¹ * (fabiusCompositionSum n : ℝ)) =
      ((2 : ℝ) ^ n)⁻¹ := by
  rw [← fabiusFunction_inverse_two_pow_eq_sum_compositions F hF n]
  apply fabiusInv_fabiusReal F hF
  constructor
  · positivity
  · exact (inv_le_one₀ (by positivity)).2 (one_le_pow₀ (by norm_num))

/-- Generic real form with literal `2^(-n)` and `2^(-choose(n,2))`
notation. -/
theorem fabiusFunction_inverse_two_pow_eq_sum_compositions_zpow
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    fabiusReal F ((2 : ℝ) ^ (-(n : ℤ))) =
      (2 : ℝ) ^ (-(n.choose 2 : ℤ)) *
        (fabiusCompositionSum n : ℝ) := by
  simpa [zpow_neg] using
    fabiusFunction_inverse_two_pow_eq_sum_compositions F hF n

/-- Literal-negative-exponent form of
`fabiusInv_two_pow_choose_mul_fabiusCompositionSum`. -/
theorem fabiusInv_fabiusCompositionSum_zpow
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    fabiusInv F hF
        ((2 : ℝ) ^ (-(n.choose 2 : ℤ)) *
          (fabiusCompositionSum n : ℝ)) =
      (2 : ℝ) ^ (-(n : ℤ)) := by
  simpa [zpow_neg] using
    fabiusInv_two_pow_choose_mul_fabiusCompositionSum F hF n

/-- Canonical bounded-Fabius specialization. -/
theorem fabius_inverse_two_pow_eq_sum_compositions (n : ℕ) :
    fabiusReal fabius (((2 : ℝ) ^ n)⁻¹) =
      ((2 : ℝ) ^ n.choose 2)⁻¹ * (fabiusCompositionSum n : ℝ) :=
  fabiusFunction_inverse_two_pow_eq_sum_compositions fabius fabius_spec n

/-- Canonical specialization with literal `2^(-n)` and
`2^(-choose(n,2))` notation. -/
theorem fabius_inverse_two_pow_eq_sum_compositions_zpow (n : ℕ) :
    fabiusReal fabius ((2 : ℝ) ^ (-(n : ℤ))) =
      (2 : ℝ) ^ (-(n.choose 2 : ℤ)) *
        (fabiusCompositionSum n : ℝ) := by
  exact fabiusFunction_inverse_two_pow_eq_sum_compositions_zpow
    fabius fabius_spec n

/-- Signed-global form for any bounded Fabius function satisfying its
defining equations. All inverse powers of two lie in `[0, 1]`, where the
global extension agrees with the bounded function. -/
theorem extendedFabius_inverse_two_pow_eq_sum_compositions
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    extendedFabius F ((2 : ℝ) ^ (-(n : ℤ))) =
      (2 : ℝ) ^ (-(n.choose 2 : ℤ)) *
        (fabiusCompositionSum n : ℝ) := by
  rw [extendedFabius_eq_fabiusReal F hF]
  · exact fabiusFunction_inverse_two_pow_eq_sum_compositions_zpow F hF n
  · constructor
    · positivity
    · rw [zpow_neg]
      exact (inv_le_one₀ (by positivity)).2 (one_le_pow₀ (by norm_num))

/-- Signed-global form. All arguments are in `[0, 1]`, where the global
extension agrees with the bounded Fabius function. -/
theorem globalFabius_inverse_two_pow_eq_sum_compositions (n : ℕ) :
    globalFabius ((2 : ℝ) ^ (-(n : ℤ))) =
      (2 : ℝ) ^ (-(n.choose 2 : ℤ)) *
        (fabiusCompositionSum n : ℝ) := by
  simpa only [globalFabius] using
    extendedFabius_inverse_two_pow_eq_sum_compositions fabius fabius_spec n

end

end Fabius
