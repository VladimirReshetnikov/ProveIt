import FabiusFunction.Arithmetic
import Mathlib.Algebra.BigOperators.Ring.List

/-!
# Pairwise partition defects

This module isolates the finite combinatorics behind the quadratic loss in
Faà di Bruno expansions normalized by a dyadic triangular scale.  A list
`r = [r₁, ..., rₖ]` records positive block sizes.  Its defect is the sum

`∑_{i < j} (rᵢ rⱼ - 1)`.

Writing `eᵢ = rᵢ - 1` reveals the useful structure

`D(r) = (k - 1) ∑ᵢ eᵢ + ∑_{i < j} eᵢ eⱼ`.

Consequently `D(r) ≥ (k - 1)(m - k)` when the block sizes sum to `m`, with
equality precisely when at most one block is larger than one.  The same
pairwise sum also recovers the triangular-number definition of the defect.

Over the nonextremal block-count range `2 ≤ k < m`, the first positive
defect is `m - 2`.  Equality occurs in the endpoint profile families
`(m - 1, 1)` and `(2, 1, ..., 1)`, which coincide when `m = 3`.

The statements are deliberately about arbitrary positive lists rather than
set partitions: no labels or ambient finite set are used by the argument.
-/

set_option autoImplicit false

namespace Fabius

/-! ## Unordered pair sums -/

/-- Sum `f x y` over the pairs of entries in a list, each pair occurring once
in list order.  Symmetry of `f` is not needed for the definition. -/
def pairSum {α β : Type*} [AddCommMonoid β] (f : α → α → β) : List α → β
  | [] => 0
  | x :: xs => (xs.map (f x)).sum + pairSum f xs

/-- The unordered-pair sum of an empty list vanishes. -/
@[simp] theorem pairSum_nil {α β : Type*} [AddCommMonoid β] (f : α → α → β) :
    pairSum f [] = 0 := rfl

/-- Expose the pairs involving the head of a list. -/
@[simp] theorem pairSum_cons {α β : Type*} [AddCommMonoid β]
    (f : α → α → β) (x : α) (xs : List α) :
    pairSum f (x :: xs) = (xs.map (f x)).sum + pairSum f xs := rfl

/-- The number of unordered pairs of list positions is `C(length, 2)`. -/
theorem pairSum_one {α : Type*} (xs : List α) :
    pairSum (fun _ _ ↦ (1 : ℕ)) xs = xs.length.choose 2 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp [pairSum, ih, choose_succ_two, add_comm]

/-- Pair summation distributes over pointwise addition. -/
theorem pairSum_add {α β : Type*} [AddCommMonoid β]
    (f g : α → α → β) (xs : List α) :
    pairSum (fun x y ↦ f x y + g x y) xs = pairSum f xs + pairSum g xs := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [pairSum_cons, ih, List.sum_map_add]
      ac_rfl

/-- Two kernels with the same values on entries of the list have the same
unordered-pair sum. -/
theorem pairSum_congr {α β : Type*} [AddCommMonoid β]
    (f g : α → α → β) (xs : List α)
    (h : ∀ x ∈ xs, ∀ y ∈ xs, f x y = g x y) :
    pairSum f xs = pairSum g xs := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have htail : pairSum f xs = pairSum g xs := by
        apply ih
        intro y hy z hz
        exact h y (by simp [hy]) z (by simp [hz])
      have hhead : xs.map (f x) = xs.map (g x) := by
        apply List.map_congr_left
        intro y hy
        exact h x (by simp) y (by simp [hy])
      simp only [pairSum_cons, htail, hhead]

/-- Mapping the entries of a list before pair summation is the same as
composing both arguments of the kernel with the map. -/
theorem pairSum_map {α γ β : Type*} [AddCommMonoid β]
    (f : γ → γ → β) (g : α → γ) (xs : List α) :
    pairSum f (xs.map g) = pairSum (fun x y ↦ f (g x) (g y)) xs := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, pairSum_cons, List.map_map, ih]
      rw [show f (g x) ∘ g = (fun y ↦ f (g x) (g y)) by rfl]

/-- Triangular numbers split across a sum with the cross term retained. -/
theorem choose_add_two (a b : ℕ) :
    (a + b).choose 2 = a.choose 2 + b.choose 2 + a * b := by
  induction b with
  | zero => simp
  | succ b ih =>
      rw [show a + (b + 1) = (a + b) + 1 by omega,
        choose_succ_two, ih, choose_succ_two]
      ring

/-- The triangular number of a sum is the sum of the individual triangular
numbers plus all pairwise products. -/
theorem choose_list_sum_two (xs : List ℕ) :
    xs.sum.choose 2 =
      (xs.map fun x ↦ x.choose 2).sum + pairSum (fun x y ↦ x * y) xs := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      rw [List.sum_cons, choose_add_two, ih]
      simp only [List.map_cons, List.sum_cons, pairSum_cons]
      have hcross : (xs.map fun y ↦ x * y).sum = x * xs.sum := by
        simpa using List.sum_map_mul_left (l := xs) (f := id) (r := x)
      rw [hcross]
      ring

/-! ## Defect and its two algebraic forms -/

/-- The contribution of two block sizes to the partition defect, written in
terms of their excesses over singleton size.  For positive `x,y` this equals
`x * y - 1`. -/
def blockPairDefect (x y : ℕ) : ℕ :=
  (x - 1) * (y - 1) + ((x - 1) + (y - 1))

/-- For positive block sizes, the excess form of a pair defect is exactly
`x * y - 1`. -/
theorem blockPairDefect_eq_mul_sub_one {x y : ℕ} (hx : 0 < x) (hy : 0 < y) :
    blockPairDefect x y = x * y - 1 := by
  have hx' : x - 1 + 1 = x := by omega
  have hy' : y - 1 + 1 = y := by omega
  have hxy : 1 ≤ x * y := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hx.ne' hy.ne')
  have hprod : blockPairDefect x y + 1 = x * y := by
    calc
      blockPairDefect x y + 1 = (x - 1 + 1) * (y - 1 + 1) := by
        rw [blockPairDefect]
        ring
      _ = x * y := by rw [hx', hy']
  omega

/-- The quadratic defect of a list of block sizes.  The excess-based
definition has no truncated-subtraction side conditions; positivity is only
needed when relating it to the conventional term `x * y - 1`. -/
def partitionDefect (r : List ℕ) : ℕ :=
  pairSum blockPairDefect r

/-- For positive block sizes, the defect is the transparent pairwise sum
`∑_{i<j} (rᵢ rⱼ - 1)`. -/
theorem partitionDefect_eq_pairSum_mul_sub_one
    {r : List ℕ} (hr : ∀ x ∈ r, 0 < x) :
    partitionDefect r = pairSum (fun x y ↦ x * y - 1) r := by
  induction r with
  | nil => simp [partitionDefect]
  | cons x xs ih =>
      have hx : 0 < x := hr x (by simp)
      have hxs : ∀ y ∈ xs, 0 < y := by
        intro y hy
        exact hr y (by simp [hy])
      have ih' : pairSum blockPairDefect xs =
          pairSum (fun x y ↦ x * y - 1) xs := by
        simpa only [partitionDefect] using ih hxs
      simp only [partitionDefect, pairSum_cons, ih']
      have hmap : xs.map (blockPairDefect x) = xs.map (fun y ↦ x * y - 1) :=
        List.map_congr_left fun y hy ↦ blockPairDefect_eq_mul_sub_one hx (hxs y hy)
      rw [hmap]

/-- The defect is a natural number and hence is nonnegative.  More informative
lower bounds appear below. -/
theorem partitionDefect_nonneg (r : List ℕ) : 0 ≤ partitionDefect r :=
  Nat.zero_le _

/-- The pairwise and triangular presentations of the defect agree without
natural-number subtraction:

`C(sum r, 2) = C(length r, 2) + ∑ C(rᵢ, 2) + D(r)`. -/
theorem choose_sum_two_eq_choose_length_add_sum_add_partitionDefect
    {r : List ℕ} (hr : ∀ x ∈ r, 0 < x) :
    r.sum.choose 2 = r.length.choose 2 +
      (r.map fun x ↦ x.choose 2).sum + partitionDefect r := by
  rw [choose_list_sum_two]
  have hproducts : pairSum (fun x y ↦ x * y) r =
      pairSum (fun x y ↦ 1 + blockPairDefect x y) r := by
    apply pairSum_congr
    intro x hx y hy
    have hdef := blockPairDefect_eq_mul_sub_one (hr x hx) (hr y hy)
    have hpos : 1 ≤ x * y :=
      Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero (hr x hx).ne' (hr y hy).ne')
    calc
      x * y = x * y - 1 + 1 := (Nat.sub_add_cancel hpos).symm
      _ = 1 + (x * y - 1) := Nat.add_comm _ _
      _ = 1 + blockPairDefect x y := by rw [hdef]
  rw [hproducts, pairSum_add, pairSum_one]
  simp only [partitionDefect]
  omega

/-- The conventional subtraction formula for the partition defect. -/
theorem partitionDefect_eq_choose_sum_sub_choose_length_sub_sum
    {r : List ℕ} (hr : ∀ x ∈ r, 0 < x) :
    partitionDefect r = r.sum.choose 2 - r.length.choose 2 -
      (r.map fun x ↦ x.choose 2).sum := by
  have h := choose_sum_two_eq_choose_length_add_sum_add_partitionDefect hr
  omega

/-- Positive block sizes have total size at least their block count. -/
theorem length_le_sum_of_pos {r : List ℕ} (hr : ∀ x ∈ r, 0 < x) :
    r.length ≤ r.sum := by
  simpa using r.card_nsmul_le_sum 1 (fun x hx ↦ hr x hx)

/-- The total excess over singleton blocks is `sum r - length r`. -/
theorem sum_map_sub_one {r : List ℕ} (hr : ∀ x ∈ r, 0 < x) :
    (r.map fun x ↦ x - 1).sum = r.sum - r.length := by
  induction r with
  | nil => simp
  | cons x xs ih =>
      have hx : 0 < x := hr x (by simp)
      have hxs : ∀ y ∈ xs, 0 < y := by
        intro y hy
        exact hr y (by simp [hy])
      have hlen := length_le_sum_of_pos hxs
      simp only [List.map_cons, List.sum_cons, List.length_cons, ih hxs]
      omega

/-- Every entry in a list occurs in exactly `length - 1` unordered pairs.
Thus the sum of `aᵢ + aⱼ` over pairs is `(length - 1) * sum a`. -/
theorem pairSum_add_eq (a : List ℕ) :
    pairSum (fun x y ↦ x + y) a = (a.length - 1) * a.sum := by
  induction a with
  | nil => simp
  | cons x xs ih =>
      cases xs with
      | nil => simp
      | cons y ys =>
          simp only [pairSum_cons, List.map_cons, List.sum_cons,
            List.length_cons, Nat.add_sub_cancel, ih]
          have hmap : (ys.map fun z ↦ x + z).sum = ys.length * x + ys.sum := by
            rw [List.sum_map_add]
            simp [Nat.mul_comm]
          rw [hmap]
          ring

/-- The linear pair contribution after applying a weight to each entry. -/
theorem pairSum_map_add_eq {α : Type*} (f : α → ℕ) (xs : List α) :
    pairSum (fun x y ↦ f x + f y) xs =
      (xs.length - 1) * (xs.map f).sum := by
  rw [← pairSum_map (fun x y : ℕ ↦ x + y) f, pairSum_add_eq]
  simp

/-- **Excess decomposition.**  The defect is its sharp linear lower bound
plus a visibly nonnegative sum of pairwise excess products. -/
theorem partitionDefect_eq_linear_add_pairwise_excess (r : List ℕ) :
    partitionDefect r =
      (r.length - 1) * (r.map fun x ↦ x - 1).sum +
        pairSum (fun x y ↦ (x - 1) * (y - 1)) r := by
  rw [partitionDefect]
  change pairSum
      (fun x y ↦ (x - 1) * (y - 1) + ((x - 1) + (y - 1))) r = _
  rw [pairSum_add, pairSum_map_add_eq]
  exact add_comm _ _

/-- **Sharp fixed-block lower bound.**  For positive blocks, the defect is at
least `(k - 1)(m - k)`, where `k` is the number of blocks and `m` their total
size. -/
theorem partitionDefect_lower_bound {r : List ℕ} (hr : ∀ x ∈ r, 0 < x) :
    (r.length - 1) * (r.sum - r.length) ≤ partitionDefect r := by
  rw [partitionDefect_eq_linear_add_pairwise_excess, sum_map_sub_one hr]
  exact Nat.le_add_right _ _

/-- The sharp lower bound with an explicitly named total size and block
count, in the form used for integer partitions. -/
theorem partitionDefect_fixed_block_bound {r : List ℕ} {m k : ℕ}
    (hr : ∀ x ∈ r, 0 < x) (hsum : r.sum = m) (hlen : r.length = k) :
    (k - 1) * (m - k) ≤ partitionDefect r := by
  simpa only [hsum, hlen] using partitionDefect_lower_bound hr

private theorem list_sum_eq_zero_iff (a : List ℕ) :
    a.sum = 0 ↔ ∀ x ∈ a, x = 0 := by
  induction a with
  | nil => simp
  | cons x xs ih => simp [ih]

/-- A natural-valued unordered-pair sum vanishes exactly when its kernel
vanishes on every pair of list positions. -/
theorem pairSum_eq_zero_iff_pairwise {α : Type*} (f : α → α → ℕ) (xs : List α) :
    pairSum f xs = 0 ↔ xs.Pairwise fun x y ↦ f x y = 0 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      rw [pairSum_cons, Nat.add_eq_zero_iff, ih, List.pairwise_cons]
      have hhead : (xs.map (f x)).sum = 0 ↔ ∀ y ∈ xs, f x y = 0 := by
        rw [list_sum_eq_zero_iff]
        simp
      exact and_congr hhead Iff.rfl

/-- A positive pair contributes zero defect exactly when both blocks are
singletons. -/
theorem blockPairDefect_eq_zero_iff {x y : ℕ} (hx : 0 < x) (hy : 0 < y) :
    blockPairDefect x y = 0 ↔ x = 1 ∧ y = 1 := by
  rw [blockPairDefect_eq_mul_sub_one hx hy]
  constructor
  · intro h
    have hle : x * y ≤ 1 := Nat.sub_eq_zero_iff_le.mp h
    have hge : 1 ≤ x * y :=
      Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hx.ne' hy.ne')
    have hone : x * y = 1 := Nat.le_antisymm hle hge
    exact ⟨Nat.eq_one_of_mul_eq_one_right hone, Nat.eq_one_of_mul_eq_one_left hone⟩
  · rintro ⟨rfl, rfl⟩
    simp

/-- The defect vanishes exactly for a list with at most one block or a list
consisting entirely of singleton blocks.  These are the two unbranched
Faà di Bruno profiles. -/
theorem partitionDefect_eq_zero_iff {r : List ℕ} (hr : ∀ x ∈ r, 0 < x) :
    partitionDefect r = 0 ↔
      r.length ≤ 1 ∨ ∀ x ∈ r, x = 1 := by
  rw [partitionDefect, pairSum_eq_zero_iff_pairwise]
  have hp : r.Pairwise (fun x y ↦ blockPairDefect x y = 0) ↔
      r.Pairwise (fun x y ↦ x = 1 ∧ y = 1) := by
    apply List.Pairwise.iff_of_mem
    intro x y hx hy
    exact blockPairDefect_eq_zero_iff (hr x hx) (hr y hy)
  rw [hp]
  constructor
  · intro h
    by_cases hlen : r.length ≤ 1
    · exact Or.inl hlen
    · right
      cases r with
      | nil => simp at hlen
      | cons x xs =>
          cases xs with
          | nil => simp at hlen
          | cons y ys =>
              rw [List.pairwise_cons] at h
              intro z hz
              rw [List.mem_cons] at hz
              rcases hz with rfl | hz
              · exact (h.1 y (by simp)).1
              · exact (h.1 z hz).2
  · rintro (hlen | hall)
    · cases r with
      | nil => simp
      | cons x xs =>
          cases xs with
          | nil => simp
          | cons y ys => simp at hlen
    · exact (List.pairwise_of_forall (R := fun _ _ : ℕ ↦ True)
          fun _ _ ↦ True.intro).imp_of_mem fun hx hy _ ↦ ⟨hall _ hx, hall _ hy⟩

/-- Two positive excesses have zero product exactly when at least one of the
corresponding blocks is a singleton. -/
theorem sub_one_mul_sub_one_eq_zero_iff {x y : ℕ} (hx : 0 < x) (hy : 0 < y) :
    (x - 1) * (y - 1) = 0 ↔ x = 1 ∨ y = 1 := by
  rw [Nat.mul_eq_zero]
  omega

/-- **Equality profile for the sharp bound.**  Equality holds exactly when
every pair of blocks contains a singleton—in other words, at most one block
is larger than one. -/
theorem partitionDefect_eq_lower_bound_iff {r : List ℕ}
    (hr : ∀ x ∈ r, 0 < x) :
    partitionDefect r = (r.length - 1) * (r.sum - r.length) ↔
      r.Pairwise (fun x y ↦ x = 1 ∨ y = 1) := by
  rw [partitionDefect_eq_linear_add_pairwise_excess, sum_map_sub_one hr]
  let E := pairSum (fun x y ↦ (x - 1) * (y - 1)) r
  have hzero : E = 0 ↔ r.Pairwise (fun x y ↦ x = 1 ∨ y = 1) := by
    dsimp only [E]
    rw [pairSum_eq_zero_iff_pairwise]
    apply List.Pairwise.iff_of_mem
    intro x y hx hy
    exact sub_one_mul_sub_one_eq_zero_iff (hr x hx) (hr y hy)
  constructor
  · intro h
    apply hzero.mp
    dsimp only [E]
    omega
  · intro h
    have := hzero.mpr h
    dsimp only [E] at this
    omega

/-- Equality in the fixed-`m`, fixed-`k` bound is equivalent to the profile
with at most one nonsingleton block. -/
theorem partitionDefect_fixed_block_eq_iff {r : List ℕ} {m k : ℕ}
    (hr : ∀ x ∈ r, 0 < x) (hsum : r.sum = m) (hlen : r.length = k) :
    partitionDefect r = (k - 1) * (m - k) ↔
      r.Pairwise (fun x y ↦ x = 1 ∨ y = 1) := by
  simpa only [hsum, hlen] using partitionDefect_eq_lower_bound_iff hr

/-! ## The first positive defect shell -/

/-- For two positive natural numbers, their product is at least their sum
minus one.  The gap is exactly the product of their excesses over one. -/
theorem add_sub_one_le_mul_of_pos {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    a + b - 1 ≤ a * b := by
  have ha' : a - 1 + 1 = a := by omega
  have hb' : b - 1 + 1 = b := by omega
  have hab : a + b - 1 = (a - 1) + (b - 1) + 1 := by omega
  have hfactor : a * b =
      (a + b - 1) + (a - 1) * (b - 1) := by
    calc
      a * b = (a - 1 + 1) * (b - 1 + 1) := by rw [ha', hb']
      _ = ((a - 1) + (b - 1) + 1) + (a - 1) * (b - 1) := by ring
      _ = (a + b - 1) + (a - 1) * (b - 1) := by rw [hab]
  rw [hfactor]
  exact Nat.le_add_right _ _

/-- Equality in `a + b - 1 ≤ a * b` occurs exactly at the two boundary
families `a = 1` or `b = 1`. -/
theorem mul_eq_add_sub_one_iff {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    a * b = a + b - 1 ↔ a = 1 ∨ b = 1 := by
  have ha' : a - 1 + 1 = a := by omega
  have hb' : b - 1 + 1 = b := by omega
  have hab : a + b - 1 = (a - 1) + (b - 1) + 1 := by omega
  have hfactor : a * b =
      (a + b - 1) + (a - 1) * (b - 1) := by
    calc
      a * b = (a - 1 + 1) * (b - 1 + 1) := by rw [ha', hb']
      _ = ((a - 1) + (b - 1) + 1) + (a - 1) * (b - 1) := by ring
      _ = (a + b - 1) + (a - 1) * (b - 1) := by rw [hab]
  rw [hfactor]
  constructor
  · intro h
    apply (sub_one_mul_sub_one_eq_zero_iff ha hb).mp
    omega
  · intro h
    have hz := (sub_one_mul_sub_one_eq_zero_iff ha hb).mpr h
    omega

/-- Over the nonextremal block-count range `2 ≤ k < m`, the fixed-block
minimum `(k - 1)(m - k)` is at least the first-shell value `m - 2`. -/
theorem firstShell_le_fixedBlockProduct {m k : ℕ} (hk : 2 ≤ k) (hkm : k < m) :
    m - 2 ≤ (k - 1) * (m - k) := by
  have hleft : 0 < k - 1 := by omega
  have hright : 0 < m - k := by omega
  have hsum : (k - 1) + (m - k) - 1 = m - 2 := by omega
  rw [← hsum]
  exact add_sub_one_le_mul_of_pos hleft hright

/-- The fixed-block product reaches the first shell only at the two endpoint
block counts: two blocks, or all but one blocks. -/
theorem fixedBlockProduct_eq_firstShell_iff {m k : ℕ}
    (hk : 2 ≤ k) (hkm : k < m) :
    (k - 1) * (m - k) = m - 2 ↔ k = 2 ∨ k = m - 1 := by
  have hleft : 0 < k - 1 := by omega
  have hright : 0 < m - k := by omega
  have hsum : (k - 1) + (m - k) - 1 = m - 2 := by omega
  rw [← hsum, mul_eq_add_sub_one_iff hleft hright]
  omega

/-- **First positive defect shell.**  A positive block-size list with between
two and `m - 1` blocks has defect at least `m - 2`. -/
theorem firstShell_le_partitionDefect {r : List ℕ} {m : ℕ}
    (hr : ∀ x ∈ r, 0 < x) (hsum : r.sum = m)
    (htwo : 2 ≤ r.length) (hproper : r.length < m) :
    m - 2 ≤ partitionDefect r := by
  refine (firstShell_le_fixedBlockProduct htwo hproper).trans ?_
  simpa only [hsum] using partitionDefect_lower_bound hr

/-- Equality on the first positive shell has exactly the endpoint block
counts and the sharp fixed-block profile: either `k = 2` or `k = m - 1`,
and at most one block is nonsingleton.  With total size `m`, these are the
profiles `(m - 1, 1)` and `(2, 1, ..., 1)`, up to ordering. -/
theorem partitionDefect_eq_firstShell_iff {r : List ℕ} {m : ℕ}
    (hr : ∀ x ∈ r, 0 < x) (hsum : r.sum = m)
    (htwo : 2 ≤ r.length) (hproper : r.length < m) :
    partitionDefect r = m - 2 ↔
      (r.length = 2 ∨ r.length = m - 1) ∧
        r.Pairwise (fun x y ↦ x = 1 ∨ y = 1) := by
  let L := (r.length - 1) * (m - r.length)
  have hshellL : m - 2 ≤ L := firstShell_le_fixedBlockProduct htwo hproper
  have hLdefect : L ≤ partitionDefect r := by
    dsimp only [L]
    simpa only [hsum] using partitionDefect_lower_bound hr
  have hLendpoints : L = m - 2 ↔
      r.length = 2 ∨ r.length = m - 1 := by
    dsimp only [L]
    exact fixedBlockProduct_eq_firstShell_iff htwo hproper
  have hprofile : partitionDefect r = L ↔
      r.Pairwise (fun x y ↦ x = 1 ∨ y = 1) := by
    dsimp only [L]
    simpa only [hsum] using partitionDefect_eq_lower_bound_iff hr
  constructor
  · intro hdefect
    have hLe : L ≤ m - 2 := by omega
    have hLeq : L = m - 2 := Nat.le_antisymm hLe hshellL
    have hDeqL : partitionDefect r = L := by omega
    exact ⟨hLendpoints.mp hLeq, hprofile.mp hDeqL⟩
  · rintro ⟨hendpoints, hp⟩
    have hLeq := hLendpoints.mpr hendpoints
    have hDeqL := hprofile.mpr hp
    omega

/-- The first-shell value is attained by the two-block profile
`(m - 1, 1)` whenever `m ≥ 3`. -/
theorem partitionDefect_twoBlock_firstShell {m : ℕ} (hm : 3 ≤ m) :
    partitionDefect [m - 1, 1] = m - 2 := by
  simp [partitionDefect, pairSum, blockPairDefect]
  omega

end Fabius
