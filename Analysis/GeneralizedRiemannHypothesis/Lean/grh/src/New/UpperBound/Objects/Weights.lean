import New.Reduction.Data.LevelAndTwists

/-!
# Harish-Chandra parameters, weights and lift diagrams of the definite spaces

A weight is given by its last entry and by the number of columns of each height of its Young diagram
at each infinite place of `E`. This file fixes the weights on the spaces `X_j` and `Y_m`. It defines
the Harish-Chandra parameters of the `X_j` and of `Y_m` in decreasing order, the highest weights
`μ(X_j)` and `μ(Y_m)`, and the diagrams of the lifts between the `X_j`. It computes the columns and
bounds the rows of these diagrams, and it shows that `μ(X_m)` and `μ(Y_m)` interlace. It also
computes `n_τ = |μ(X_m)_τ| - |μ(Y_m)_τ|`, where `|·|` is the sum of the entries.

## Main definitions and results

* `New.Data.columnCount`, `New.Data.lastEntry`: the columns and the last entry of the weight on
  `X_j`.
* `New.Data.keptColumns`, `New.Data.columnsY`: the columns of the weight on `Y_m`, obtained by
  branching.
* `New.Data.paramX`, `New.Data.weightX`, `New.Data.liftDiagram`: the doubled parameters and the
  weights of the `X_j`, and the diagrams of the lifts.
* `New.Data.weightX_eq`, `New.Data.weightY_eq`: the weights in terms of their columns.
* `New.Data.branchExponent_eq`: the formula for `n_τ`.

Notions from other files:
* `New.Data`: data `D` for parameters `P : New.Parameters`. They give a CM field `E`, the number
  `m = D.m` of lifts and a rank `r = D.r`. From these come `k = D.k = r + 1 - m`, `t = D.t = 5 r`,
  the ranks `n_j = D.n j = k + j (t + 1)` and the gap `Δ = D.gap = 2 * D.halfGap = 2 r ^ 8`.
* `X_j`, `Y_m`: the standard definite hermitian spaces over `E` of ranks `n_j` and `n_m - 1`. Lift
  `j + 1` is the theta lift from forms on `U(X_j)` to forms on `U(X_{j+1})`. Branching is the
  restriction of representations from `U(X_m)` to `U(Y_m)`. This file has only their weights.
* `New.Data.Φ`: the set of infinite places of `E`.
* `New.Data.a`, `New.Data.aPlaces`: the integer `a = x b`, for the scales `x` and `b` of the data,
  and the set of `a`-places, the places `≡ 1` modulo `P.q₀`.
* `New.Data.liftWeight`: the weight `κ_j(σ) = κ(σ) + (j + 1/2) Δ` at `σ`, with `κ = D.weight`. It is
  not to be confused with the column count `New.Data.columnCount`.
* `New.Data.targetParameter`: the sequence `λ^Y = (k/2 - 1, …, 1 - k/2; -κ_{1/2}, -κ_{3/2}, …)` at a
  place, where `κ_{i - 1/2} = κ_i - Δ / 2`.
-/

noncomputable section

/-! ## The column diagrams of the weights -/

namespace New.Data

variable {P : Parameters} (D : Data P)

/-- The number of columns of height `h` at the place `τ` of the weight on the definite space `X_j`
of rank `n_j = k + j (t + 1)`, for `h < n_j` (see `weightX_eq`); here `k = D.k` and `t = D.t`. For
`h = 1` it is `D.a` at the places in `D.aPlaces` and `0` elsewhere; for `h = k ≠ 1` it is
`κ_1(τ) − ⌊(k + t + 1) / 2⌋`, with `κ_1(τ) = D.liftWeight 1 τ`; for `h > k` with `h ≡ k` mod `t + 1`
it is the gap `D.gap` minus `t + 1`; else it is `0`. Subtraction is that of natural numbers. -/
def columnCount (τ : D.Φ) (h : ℕ) : ℕ :=
  if h = 1 then
    (if τ ∈ D.aPlaces then D.a else 0)
  else if h = D.k then
    D.liftWeight 1 τ - (D.k + D.t + 1) / 2
  else if D.k < h ∧ D.t + 1 ∣ h - D.k then D.gap - (D.t + 1) else 0

/-- Bound on the number of columns of height `h` at `τ`, with the count at height one replaced by
`a`: `D.columnCount τ h` (or `a` if `h = 1`) is at most `a` (if `h = 1`) plus `D.liftWeight 1 τ` (if
`h = D.k`) plus the gap `D.gap`. -/
lemma columnCount_le (τ : D.Φ) (h a : ℕ) :
    (if h = 1 then a else D.columnCount τ h) ≤
      (if h = 1 then a else 0) + (if h = D.k then D.liftWeight 1 τ else 0) + D.gap := by
  grind [columnCount]

/-- The last entry of the weight on `X_j` at the place `τ` (see `weightX_eq`): it is `0` for
`j = 0`, else `⌊n_{j−1} / 2⌋ − κ_j(τ)`, with `n_j = D.n j` the rank `k + j (t + 1)` and
`κ_j(τ) = D.liftWeight j τ`. -/
def lastEntry (j : ℕ) (τ : D.Φ) : ℤ := if j = 0 then 0 else (D.n (j - 1) / 2 - D.liftWeight j τ : ℤ)

/-- Let `m = D.m` be the number of lifts, and let `X_m`, `Y_m` be the definite spaces of ranks `n_m`
and `n_m - 1`. For `h < n_m` this is the number of columns of height `h` of the weight on `X_m` that
keep their height under branching to `Y_m` (see `weightY_eq`). It is `Δ / 2 − (t + 1) / 2`, with
`Δ / 2 = D.halfGap` half the gap, if `h ≥ k` and `h ≡ k` mod `t + 1`, and `0` otherwise. -/
def keptColumns (h : ℕ) : ℕ := if D.k ≤ h ∧ D.t + 1 ∣ h - D.k then D.reducedHalfGap else 0

/-- The number of columns of height `h` at `τ` of the weight on `Y_m`, for `h < n_m - 1` (see
`weightY_eq`): the kept columns of height `h`, and the columns of height `h + 1` of the weight on
`X_m` that are not kept. -/
def columnsY (τ : D.Φ) (h : ℕ) : ℕ :=
  D.keptColumns h + (D.columnCount τ (h + 1) - D.keptColumns (h + 1))

end New.Data

/-!
## Parameters, weights and lift diagrams of the definite spaces

Parameters are doubled, so that they are integers; weights are not doubled. Entries and rows are
numbered from `0`.
-/

section Diagrams

open Finset

namespace New

/-- Twice the entry `p` of the block `[n] = ((n - 1) / 2, (n - 3) / 2, …, (1 - n) / 2)`. -/
def twiceBlockEntry (n p : ℕ) : ℤ := n - 1 - 2 * p

/-- The entries of the block `[n]` have sum `0`. -/
lemma sum_twiceBlockEntry (n : ℕ) : ∑ p ∈ range n, twiceBlockEntry n p = 0 := by
  have h_gauss : (∑ p ∈ range n, (p : ℤ)) * 2 = n * (n - 1) := by
    induction n with
    | zero => simp
    | succ n ih => grind [sum_range_succ]
  simp only [twiceBlockEntry, sum_sub_distrib, sum_const, card_range, ← mul_sum, nsmul_eq_mul]
  linarith

namespace Data

variable {P : Parameters} (D : Data P)

lemma n_zero : D.n 0 = D.k := by simp [n]

lemma n_succ (j : ℕ) : D.n (j + 1) = D.n j + (D.t + 1) := by grind [n]

lemma k_le_n (j : ℕ) : D.k ≤ D.n j := by simp [n]

lemma n_pos (j : ℕ) : 0 < D.n j := D.k_pos.trans_le (D.k_le_n j)

/-- Each rank `n_j = k + j (t + 1)` is even, as `k` is even and `t` is odd. -/
lemma n_even (j : ℕ) : Even (D.n j) := D.k_even.add (D.t_odd.add_one.mul_left j)

lemma liftWeight_add (j : ℕ) (τ : D.Φ) (i : ℕ) :
    D.liftWeight (j + i) τ = D.liftWeight j τ + i * D.gap := by
  simp only [liftWeight_eq]
  ring

lemma liftWeight_succ (j : ℕ) (τ : D.Φ) : D.liftWeight (j + 1) τ = D.liftWeight j τ + D.gap := by
  rw [liftWeight_add, one_mul]

lemma halfGap_le_liftWeight (j : ℕ) (τ : D.Φ) :
    D.halfGap ≤ D.liftWeight j τ := by simp [liftWeight_eq]

/-! ### The parameters and weights of the spaces `X_j` -/

/-- The number `a_τ`: it is `a` at the places in `D.aPlaces` (the `a`-places) and `0` elsewhere. -/
def firstRowExcess (τ : D.Φ) : ℕ := if τ ∈ D.aPlaces then D.a else 0

/-- Twice the Harish-Chandra parameters of the `X_j` at the place `τ`, in decreasing order: first
`λ^X = [k] + (a_τ, 0, …, 0)`, then the blocks `-κ_i + [t + 1]` for `i = 1, 2, …`. The parameter of
`X_j` consists of the first `n_j` entries. That they decrease follows from `weightX_eq`. -/
def paramX (τ : D.Φ) (p : ℕ) : ℤ :=
  if p < D.k then
    twiceBlockEntry D.k p + if p = 0 then 2 * (D.firstRowExcess τ : ℤ) else 0
  else
    twiceBlockEntry (D.t + 1) ((p - D.k) % (D.t + 1)) -
      2 * D.liftWeight ((p - D.k) / (D.t + 1) + 1) τ

/-- The sequence `D.paramX τ` lists twice the Harish-Chandra parameters of the definite spaces `X_i`
at the place `τ`. For `b < t + 1`, with `t = D.t`, its entry at position `n_j + b` is twice entry
`b` of the block `-κ_{j+1} + [t + 1]`. Here `n_j = D.n j` is the rank of `X_j`,
`κ_{j+1} = D.liftWeight (j + 1) τ` and `[t + 1] = (t / 2, (t - 2) / 2, …, -t / 2)`. -/
lemma paramX_block (j : ℕ) (τ : D.Φ) {b : ℕ} (hb : b < D.t + 1) :
    D.paramX τ (D.n j + b) = twiceBlockEntry (D.t + 1) b - 2 * D.liftWeight (j + 1) τ := by
  have h_le : D.k ≤ D.n j + b := (D.k_le_n j).trans (Nat.le_add_right _ _)
  have h_index : D.n j + b - D.k = b + (D.t + 1) * j := by grind [n]
  have h_mod : (b + (D.t + 1) * j) % (D.t + 1) = b := by simp [Nat.mod_eq_of_lt hb]
  have h_div : (b + (D.t + 1) * j) / (D.t + 1) = j := by
    rw [Nat.add_mul_div_left _ _ D.t.succ_pos, Nat.div_eq_of_lt hb, zero_add]
  rw [paramX, ite_eq_right h_le.not_gt, h_index, h_mod, h_div]

/-- Entry `p` of the highest weight `μ(X_j)` at the place `τ`: the decreasing parameter less the
block `[n_j]`, where `n_j = D.n j` is the rank of `X_j`. Both `D.paramX τ` and `twiceBlockEntry` are
doubled, and the division by `2` is exact (`two_mul_weightX`). -/
def weightX (j : ℕ) (τ : D.Φ) (p : ℕ) : ℤ := (D.paramX τ p - twiceBlockEntry (D.n j) p) / 2

/-- The division by `2` in the definition of the weight `μ(X_j) = D.weightX j τ` is exact: twice the
weight is the doubled parameter `D.paramX τ` less the doubled block `[n_j]`. -/
lemma two_mul_weightX (j : ℕ) (τ : D.Φ) {p : ℕ} :
    2 * D.weightX j τ p = D.paramX τ p - twiceBlockEntry (D.n j) p := by
  obtain ⟨u, hu⟩ : Even (D.n j) := D.n_even j
  obtain ⟨v, hv⟩ : Even D.k := D.k_even
  obtain ⟨s, hs⟩ : Odd D.t := D.t_odd
  -- The ranks `k`, `t + 1` and `n_j` are even, so both terms on the right are odd.
  simp only [weightX, paramX, twiceBlockEntry]
  split_ifs <;> omega

/-- Row `p` at the place `τ` of the diagram `μ_{j+1}^+ = μ(X_j) + κ_{j+1} - n_{j+1} / 2` of lift
`j + 1`, the theta lift from forms on `U(X_j)` to forms on `U(X_{j+1})`. Here `μ(X_j)` is the weight
`D.weightX j τ`, `κ_{j+1} = D.liftWeight (j + 1) τ` and `n_j = D.n j` is the rank of `X_j`. The
diagram has `n_j` rows and is continued by `0`. -/
def liftDiagram (j : ℕ) (τ : D.Φ) (p : ℕ) : ℤ :=
  if p < D.n j then D.weightX j τ p + D.liftWeight (j + 1) τ - D.n (j + 1) / 2 else 0

/-- For each entry `p < n_{j+1}`, the weight `μ(X_{j+1})` is
`(μ_{j+1}^+, 0, …, 0) + n_j / 2 - κ_{j+1}`, where `μ_{j+1}^+` is `D.liftDiagram j τ`, `n_j` is the
rank `D.n j` and `κ_{j+1}` is `D.liftWeight (j + 1) τ`. -/
lemma weightX_succ (j : ℕ) (τ : D.Φ) {p : ℕ} (hp : p < D.n (j + 1)) :
    D.weightX (j + 1) τ p = D.liftDiagram j τ p + (D.n j / 2 - D.liftWeight (j + 1) τ) := by
  obtain ⟨s, hs⟩ : Odd D.t := D.t_odd
  have h_rank : D.n (j + 1) = D.n j + (D.t + 1) := D.n_succ j
  rcases lt_or_ge p (D.n j) with h_old | h_new
  · -- The first `n_j` entries of `[n_{j+1}]` are `[n_j] + (t + 1) / 2`.
    have h_shift : twiceBlockEntry (D.n (j + 1)) p = twiceBlockEntry (D.n j) p + (D.t + 1) := by
      grind [twiceBlockEntry]
    rw [liftDiagram, ite_eq_left h_old, weightX, weightX, h_shift]
    omega
  · -- The last `t + 1` entries of `[n_{j+1}]` are `[t + 1] - n_j / 2`.
    obtain ⟨b, rfl⟩ : ∃ b, p = D.n j + b := Nat.exists_eq_add_of_le h_new
    have h_shift :
        twiceBlockEntry (D.n (j + 1)) (D.n j + b) = twiceBlockEntry (D.t + 1) b - D.n j := by
      grind [twiceBlockEntry]
    rw [liftDiagram, ite_eq_right h_new.not_gt, weightX, h_shift, D.paramX_block j τ (by omega)]
    omega

/-- For `p < k` the rows of the first diagram are given by
`μ_1^+ = (a_τ, 0, …, 0) + κ_1 - n_1 / 2`, where `a_τ` is `D.firstRowExcess τ`, `κ_1` is
`D.liftWeight 1 τ` and `n_1` is the rank `D.n 1`. -/
lemma liftDiagram_zero (τ : D.Φ) {p : ℕ} (hp : p < D.k) :
    D.liftDiagram 0 τ p =
      (if p = 0 then (D.firstRowExcess τ : ℤ) else 0) + (D.liftWeight 1 τ - D.n 1 / 2) := by
  grind [liftDiagram, weightX, n_zero, paramX]

/-- The recursion `μ_{j+2}^+ = (μ_{j+1}^+, 0, …, 0) + Δ - t - 1` of the lift diagrams, in the rows
`p < n_{j+1}`: each further lift adds the gap `Δ = D.gap` less the step `t + 1` of the ranks. -/
lemma liftDiagram_succ (j : ℕ) (τ : D.Φ) {p : ℕ} (hp : p < D.n (j + 1)) :
    D.liftDiagram (j + 1) τ p = D.liftDiagram j τ p + (D.gap - (D.t + 1)) := by
  have h_ranks : D.n (j + 1 + 1) = D.n j + 2 * (D.t + 1) := by grind [n_succ]
  rw [liftDiagram, ite_eq_left hp, D.weightX_succ j τ hp, D.liftWeight_succ (j + 1), h_ranks]
  -- Halving `n_j + 2 (t + 1)` gives `n_j / 2 + (t + 1)`.
  omega

/-! ### The columns and rows of the diagrams -/

lemma columnCount_one (τ : D.Φ) : D.columnCount τ 1 = D.firstRowExcess τ := by
  simp [columnCount, firstRowExcess]

lemma one_lt_k : 1 < D.k := by grind [D.ten_thousand_le_m, D.hundred_mul_m_le_k]

/-- There are `κ_1 - n_1 / 2` columns of height `k`; this number is not negative. -/
lemma cast_columnCount_k (τ : D.Φ) : (D.columnCount τ D.k : ℤ) = D.liftWeight 1 τ - D.n 1 / 2 := by
  have h_le : D.k + D.t + 1 ≤ D.liftWeight 1 τ :=
    D.k_add_t_add_one_le_halfGap.trans (D.halfGap_le_liftWeight 1 τ)
  rw [columnCount, ite_eq_right D.one_lt_k.ne', ite_eq_left rfl, n_succ, n_zero]
  omega

/-- There are `Δ - t - 1` columns of height `n_{j+1}`; this number is not negative. -/
lemma cast_columnCount_n_succ (j : ℕ) (τ : D.Φ) :
    (D.columnCount τ (D.n (j + 1)) : ℤ) = D.gap - (D.t + 1) := by
  have h_le : D.k + D.t + 1 ≤ D.halfGap := D.k_add_t_add_one_le_halfGap
  have h_lt : D.k < D.n (j + 1) := by grind [n_succ, D.k_le_n j]
  have h_dvd : D.t + 1 ∣ D.n (j + 1) - D.k := by simp [n]
  rw [columnCount, ite_eq_right (D.one_lt_k.trans h_lt).ne', ite_eq_right h_lt.ne',
    ite_eq_left ⟨h_lt, h_dvd⟩, Data.gap]
  omega

/-- No column has a height below `k` other than `1`. -/
lemma columnCount_eq_zero_of_lt_k (τ : D.Φ) {u : ℕ} (h_one : u ≠ 1) (hu : u < D.k) :
    D.columnCount τ u = 0 := by
  simp [columnCount, h_one, hu.ne, hu.not_gt]

/-- A height `u` strictly between `n_j` and `n_{j+1}` is none of the ranks `n_i`: the step
`t + 1` of the ranks does not divide `u - k`. -/
lemma not_dvd_sub_k (j : ℕ) {u : ℕ} (hu : u ∈ Ioo (D.n j) (D.n (j + 1))) : ¬D.t + 1 ∣ u - D.k := by
  rw [mem_Ioo, n, n, mul_comm j, mul_comm (j + 1)] at hu
  exact Nat.not_dvd_of_lt_of_lt_mul_succ (k := j) (by omega) (by omega)

/-- No column has a height strictly between the ranks `n_j` and `n_{j+1}`. -/
lemma columnCount_eq_zero_of_mem_Ioo (j : ℕ) (τ : D.Φ) {u : ℕ}
    (hu : u ∈ Ioo (D.n j) (D.n (j + 1))) :
    D.columnCount τ u = 0 := by
  have h_lt : D.k < u := (D.k_le_n j).trans_lt (mem_Ioo.1 hu).1
  simp [columnCount, (D.one_lt_k.trans h_lt).ne', h_lt.ne', D.not_dvd_sub_k j hu]

/-- The number of columns of height strictly between `p` and `k` is `a_τ = D.firstRowExcess τ` for
`p = 0` and `0` otherwise, as only the height `1` occurs below `k`. -/
lemma cast_sum_columnCount_Ioo_k (τ : D.Φ) {p : ℕ} :
    ((∑ u ∈ Ioo p D.k, D.columnCount τ u : ℕ) : ℤ) =
      if p = 0 then (D.firstRowExcess τ : ℤ) else 0 := by
  rw [sum_eq_ite 1 fun u hu h_one ↦ D.columnCount_eq_zero_of_lt_k τ h_one (mem_Ioo.1 hu).2]
  simp [columnCount_one, D.one_lt_k]

/-- For `p < n_j`, the columns of height strictly between `p` and `n_{j+1}` are those of height
strictly between `p` and `n_j` and those of height `n_j`. -/
lemma sum_columnCount_Ioo_succ (j : ℕ) (τ : D.Φ) {p : ℕ} (hp : p < D.n j) :
    ∑ u ∈ Ioo p (D.n (j + 1)), D.columnCount τ u =
      ∑ u ∈ Ioo p (D.n j), D.columnCount τ u + D.columnCount τ (D.n j) := by
  have h_subset : Ioc p (D.n j) ⊆ Ioo p (D.n (j + 1)) := Ioc_subset_Ioo_right (by simp [n_succ])
  have h_zero : ∀ u ∈ Ioo p (D.n (j + 1)), u ∉ Ioc p (D.n j) → D.columnCount τ u = 0 :=
    fun u hu hu_not_mem ↦ D.columnCount_eq_zero_of_mem_Ioo j τ (by grind)
  rw [sum_Ioo_add_eq_sum_Ioc hp, sum_subset h_subset h_zero]

/-- Let `μ_{j+1}^+ = D.liftDiagram j τ` be the Young diagram of lift `j + 1` at the place `τ`. It
has `D.columnCount τ u` columns of each height `u` below the rank `n_{j+1} = D.n (j + 1)`, and no
others: row `p`, numbered from `0`, has one box for each such column of height above `p`. The
numbers `D.columnCount τ u` are common to all lifts; only the range of heights depends on `j`. -/
lemma liftDiagram_eq_sum_columnCount (j : ℕ) (τ : D.Φ) (p : ℕ) :
    D.liftDiagram j τ p = (∑ u ∈ Ioo p (D.n (j + 1)), D.columnCount τ u : ℕ) := by
  -- The rows from `n_j` on are empty, and no column has a height strictly between `n_j` and
  -- `n_{j+1}`.
  have h_short (i : ℕ) (hp : D.n i ≤ p) :
      D.liftDiagram i τ p = (∑ u ∈ Ioo p (D.n (i + 1)), D.columnCount τ u : ℕ) := by
    rw [liftDiagram, ite_eq_right hp.not_gt, sum_eq_zero, Nat.cast_zero]
    exact fun u hu ↦ D.columnCount_eq_zero_of_mem_Ioo i τ (Ioo_subset_Ioo_left hp hu)
  induction j with
  | zero =>
    rcases le_or_gt (D.n 0) p with hp | hp
    · exact h_short 0 hp
    · rw [D.liftDiagram_zero τ (hp.trans_eq D.n_zero), D.sum_columnCount_Ioo_succ 0 τ hp, n_zero,
        Nat.cast_add, cast_sum_columnCount_Ioo_k, cast_columnCount_k]
  | succ j ih =>
    rcases le_or_gt (D.n (j + 1)) p with hp | hp
    · exact h_short (j + 1) hp
    · rw [D.liftDiagram_succ j τ hp, ih, D.sum_columnCount_Ioo_succ (j + 1) τ hp, Nat.cast_add,
        cast_columnCount_n_succ]

/-- Let `j < D.m`, where `D.m` is the number of lifts. Row `p` of the diagram
`μ_{j+1}^+ = D.liftDiagram j τ` of lift `j + 1` has a bound that depends on `p`. For `p = 0` the row
is at most `a_τ + κ_{j+1}`. For `0 < p < D.k` it is at most `κ_{j+1}`. Otherwise it is at most
`D.m * Δ`. -/
lemma liftDiagram_le {j : ℕ} (τ : D.Φ) (hj : j < D.m) (p : ℕ) :
    D.liftDiagram j τ p ≤
      if p = 0 then (D.firstRowExcess τ + D.liftWeight (j + 1) τ : ℤ)
      else if p < D.k then (D.liftWeight (j + 1) τ : ℤ) else D.m * D.gap := by
  -- There are at most `κ_1` columns of height `k`, and each further lift adds at most `Δ` columns.
  have h_count (i : ℕ) : D.liftDiagram i τ p ≤ (if p = 0 then (D.firstRowExcess τ : ℤ) else 0) +
      (if p < D.k then (D.liftWeight 1 τ : ℤ) else 0) + i * D.gap := by
    induction i with
    | zero =>
      rcases lt_or_ge p D.k with hp | hp
      · rw [D.liftDiagram_zero τ hp, ite_eq_left hp]
        omega
      · rw [liftDiagram, n_zero, ite_eq_right hp.not_gt]
        positivity
    | succ i ih =>
      rcases lt_or_ge p (D.n (i + 1)) with hp | hp
      · grind [D.liftDiagram_succ i τ hp]
      · rw [liftDiagram, ite_eq_right hp.not_gt]
        positivity
  have h_weight : D.liftWeight (j + 1) τ = D.liftWeight 1 τ + j * D.gap := by
    rw [add_comm j, liftWeight_add]
  have h_gap : (j * D.gap : ℤ) ≤ D.m * D.gap := by gcongr
  -- Compare the two bounds in the three ranges of rows.
  grind [h_count j, D.k_pos]

/-- The weight `μ(X_j)` at `τ` has `D.columnCount τ u` columns of each height `u < n_j`, and its
last entry is `D.lastEntry j τ`: for `p < n_j` the entry `p` is the last entry plus the number of
columns of height above `p`. -/
lemma weightX_eq (j : ℕ) (τ : D.Φ) {p : ℕ} (hp : p < D.n j) :
    D.weightX j τ p = D.lastEntry j τ + (∑ u ∈ Ioo p (D.n j), D.columnCount τ u : ℕ) := by
  cases j with
  | zero =>
    rw [n_zero] at hp ⊢
    have h_double : 2 * D.weightX 0 τ p = 2 * if p = 0 then (D.firstRowExcess τ : ℤ) else 0 := by
      simp [two_mul_weightX, paramX, n_zero, hp]
    rw [cast_sum_columnCount_Ioo_k, lastEntry, ite_eq_left rfl, zero_add]
    omega
  | succ j =>
    rw [D.weightX_succ j τ hp, liftDiagram_eq_sum_columnCount, add_comm, lastEntry,
      ite_eq_right j.succ_ne_zero, Nat.add_sub_cancel]

/-- The last entry of the weight `μ(X_j)` at `τ` is `n_{j+1} / 2 - κ_{j+1}` plus the number
`D.columnCount τ (D.n j)` of columns of full height `n_j` in the diagram `D.liftDiagram j τ` of lift
`j + 1`, which has `n_j` rows. Here `n_j = D.n j` is the (even) rank of `X_j` and
`κ_{j+1} = D.liftWeight (j + 1) τ` is the weight of the character of lift `j + 1`. -/
lemma lastEntry_eq (j : ℕ) (τ : D.Φ) :
    D.lastEntry j τ = D.n (j + 1) / 2 - D.liftWeight (j + 1) τ + D.columnCount τ (D.n j) := by
  have h_last : D.n j - 1 < D.n j := Nat.sub_one_lt (D.n_pos j).ne'
  have h_empty : Ioo (D.n j - 1) (D.n j) = ∅ := by
    grind
  -- The last row of the lift diagram has one box for each column of height `n_j`.
  have h_row : D.liftDiagram j τ (D.n j - 1) = D.columnCount τ (D.n j) := by
    simp [liftDiagram_eq_sum_columnCount, D.sum_columnCount_Ioo_succ j τ h_last, h_empty]
  have h_entry : D.weightX j τ (D.n j - 1) = D.lastEntry j τ := by
    simp [D.weightX_eq j τ h_last, h_empty]
  have h_diagram : D.liftDiagram j τ (D.n j - 1) =
      D.lastEntry j τ + D.liftWeight (j + 1) τ - D.n (j + 1) / 2 := by
    rw [liftDiagram, ite_eq_left h_last, h_entry]
  omega

/-! ### The parameter and the weight of `Y_m` -/

/-- The first `k - 1` entries of the sequence `λ^Y = D.targetParameter τ` form the block
`[k - 1] = (k / 2 - 1, …, 1 - k / 2)`, where `k = D.k` is the (even) rank of `X_0`; both sides are
doubled. -/
lemma two_mul_targetParameter_of_lt (τ : D.Φ) {p : ℕ} (hp : p + 1 < D.k) :
    2 * D.targetParameter τ p = twiceBlockEntry (D.k - 1) p := by
  obtain ⟨v, hv⟩ : Even D.k := D.k_even
  rw [targetParameter, ite_eq_left hp, twiceBlockEntry]
  omega

/-- The entry `k - 1 + i` (with `k = D.k`) of the parameter `λ^Y = D.targetParameter τ` is
`-κ_{i + 1/2} = Δ / 2 - κ_{i+1}`, where `Δ / 2 = D.halfGap` and
`κ_{i+1} = D.liftWeight (i + 1) τ`. -/
lemma targetParameter_k_sub_one_add (τ : D.Φ) (i : ℕ) :
    D.targetParameter τ (D.k - 1 + i) = D.halfGap - D.liftWeight (i + 1) τ := by
  have hk : 0 < D.k := D.k_pos
  rw [targetParameter_eq, ite_eq_right (by omega), show D.k - 1 + i + 2 - D.k = i + 1 by omega]

/-- Twice the Harish-Chandra parameter of `Y_m` at the place `τ`, in decreasing order: first
`[k - 1]`, then for `i = 1, 2, …` the entry `-κ_{i - 1/2}` followed by the block `-κ_i + [t]`. Here
`[n] = ((n - 1) / 2, …, (1 - n) / 2)` is the block of `twiceBlockEntry`, `κ_i = D.liftWeight i τ`
and `κ_{i - 1/2} = κ_i - D.halfGap`. The block `[k - 1]` and the `-κ_{i - 1/2}` are the entries of
`D.targetParameter τ`. The parameter consists of the first `n_m - 1` entries. -/
def sortedParamY (τ : D.Φ) (p : ℕ) : ℤ :=
  if p + 1 < D.k then
    2 * D.targetParameter τ p
  else if D.t + 1 ∣ p + 1 - D.k then
    2 * D.targetParameter τ (D.k - 1 + (p + 1 - D.k) / (D.t + 1))
  else
    twiceBlockEntry D.t ((p + 1 - D.k) % (D.t + 1) - 1) -
      2 * D.liftWeight ((p + 1 - D.k) / (D.t + 1) + 1) τ

/-- In `D.sortedParamY τ`, twice the Harish-Chandra parameter of `Y_m` (the definite space of rank
`n_m - 1`, `m = D.m`) at `τ` in decreasing order, entry `k - 1 + j` of `λ^Y = D.targetParameter τ`
stands at position `n_j - 1`. Here `n_j = D.n j = k + j (t + 1)` with `k = D.k` and `t = D.t`; both
sides are doubled. -/
lemma sortedParamY_n_sub_one (j : ℕ) (τ : D.Φ) :
    D.sortedParamY τ (D.n j - 1) = 2 * D.targetParameter τ (D.k - 1 + j) := by
  have hk : 0 < D.k := D.k_pos
  have h_index : D.n j - 1 + 1 - D.k = (D.t + 1) * j := by
    rw [n, mul_comm]
    omega
  have h_not_lt : ¬D.n j - 1 + 1 < D.k := by grind [D.k_le_n j]
  rw [sortedParamY, ite_eq_right h_not_lt, h_index, ite_eq_left (dvd_mul_right _ _),
    Nat.mul_div_cancel_left _ D.t.succ_pos]

/-- In `D.sortedParamY τ`, twice the Harish-Chandra parameter of `Y_m` at `τ` in decreasing order,
entry `b < t` of the block `-κ_{j+1} + [t]` stands at position `n_j + b`, with `t = D.t`; both sides
are doubled. -/
lemma sortedParamY_block (j : ℕ) (τ : D.Φ) {b : ℕ} (hb : b < D.t) :
    D.sortedParamY τ (D.n j + b) = twiceBlockEntry D.t b - 2 * D.liftWeight (j + 1) τ := by
  have h_index : D.n j + b + 1 - D.k = b + 1 + (D.t + 1) * j := by
    rw [n, mul_comm]
    omega
  have h_not_lt : ¬D.n j + b + 1 < D.k := by grind [D.k_le_n j]
  have h_lt : b + 1 < D.t + 1 := Nat.succ_lt_succ hb
  have h_mod : (b + 1 + (D.t + 1) * j) % (D.t + 1) = b + 1 := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h_lt]
  have h_div : (b + 1 + (D.t + 1) * j) / (D.t + 1) = j := by
    rw [Nat.add_mul_div_left _ _ D.t.succ_pos, Nat.div_eq_of_lt h_lt, zero_add]
  simp [sortedParamY, h_not_lt, h_index, Nat.dvd_iff_mod_eq_zero, h_mod, h_div]

/-- Entry `p` of the highest weight `μ(Y_m)` at the place `τ`: the decreasing parameter less the
block `[n] = ((n - 1) / 2, …, (1 - n) / 2)` for the rank `n = n_m - 1` of `Y_m`. Both
`D.sortedParamY τ` and `twiceBlockEntry` are doubled, and the division by `2` is exact
(`two_mul_weightY`). -/
def weightY (τ : D.Φ) (p : ℕ) : ℤ := (D.sortedParamY τ p - twiceBlockEntry (D.n D.m - 1) p) / 2

/-- Let `λ`, `λ'` be the decreasing Harish-Chandra parameters of `X_m` and `Y_m` at the place `τ`,
so that `D.paramX τ` and `D.sortedParamY τ` are `2 λ` and `2 λ'`, with entries numbered from `0`.
Then `λ'_p - λ_{p+1} - 1 / 2` is the number `D.keptColumns (p + 1)` of columns of height `p + 1` of
the weight on `X_m` that keep their height under branching to `Y_m`; both sides are doubled. -/
lemma sortedParamY_sub_paramX (τ : D.Φ) (p : ℕ) :
    D.sortedParamY τ p - D.paramX τ (p + 1) - 1 = 2 * D.keptColumns (p + 1) := by
  obtain ⟨s, hs⟩ : ∃ s : ℕ, D.t = 2 * s + 1 := D.t_odd
  have h_gap : D.k + D.t + 1 ≤ D.halfGap := D.k_add_t_add_one_le_halfGap
  rw [sortedParamY, paramX, keptColumns]
  by_cases h_head : p + 1 < D.k
  · -- `λ'_p` is an entry of `[k - 1]`.
    simp only [ite_eq_left h_head, D.two_mul_targetParameter_of_lt τ h_head, h_head.not_ge,
      false_and, twiceBlockEntry, p.succ_ne_zero, ite_false]
    omega
  by_cases h_dvd : D.t + 1 ∣ p + 1 - D.k
  · -- `λ'_p` is an entry `-κ_{i - 1/2}`.
    have h_kept : D.k ≤ p + 1 ∧ D.t + 1 ∣ p + 1 - D.k := ⟨not_lt.1 h_head, h_dvd⟩
    simp only [ite_eq_right h_head, ite_eq_left h_dvd, ite_eq_left h_kept,
      targetParameter_k_sub_one_add, Nat.mod_eq_zero_of_dvd h_dvd, twiceBlockEntry, reducedHalfGap]
    omega
  · -- `λ'_p` lies in a block `-κ_i + [t]`.
    have h_mod : (p + 1 - D.k) % (D.t + 1) ≠ 0 := mt Nat.dvd_of_mod_eq_zero h_dvd
    simp only [ite_eq_right h_head, h_dvd, and_false, ite_false, twiceBlockEntry]
    omega

/-- The block `[n_m - 1]` is `[n_m]` without its first entry, raised by `1 / 2`; both sides are
doubled. Here `[n] = ((n - 1) / 2, …, (1 - n) / 2)` and `n_m = D.n D.m` is the rank of `X_m`. -/
lemma twiceBlockEntry_n_sub_one (p : ℕ) :
    twiceBlockEntry (D.n D.m - 1) p = twiceBlockEntry (D.n D.m) (p + 1) + 1 := by
  grind [twiceBlockEntry, D.n_pos D.m]

/-- The highest weights `μ = μ(X_m)` and `μ' = μ(Y_m)` at `τ` satisfy
`μ'_p = μ_{p+1} + D.keptColumns (p + 1)`, where the last term counts the columns of height `p + 1`
that keep their height under branching. -/
lemma weightY_eq_weightX_add (τ : D.Φ) (p : ℕ) :
    D.weightY τ p = D.weightX D.m τ (p + 1) + D.keptColumns (p + 1) := by
  have h_param : D.sortedParamY τ p - D.paramX τ (p + 1) - 1 = 2 * D.keptColumns (p + 1) :=
    D.sortedParamY_sub_paramX τ p
  rw [weightY, weightX, twiceBlockEntry_n_sub_one]
  omega

/-- The division by `2` in the definition of the weight `μ(Y_m) = D.weightY τ` is exact: twice the
weight is the doubled parameter `D.sortedParamY τ` less the doubled block `[n_m - 1]`. -/
lemma two_mul_weightY (τ : D.Φ) {p : ℕ} :
    2 * D.weightY τ p = D.sortedParamY τ p - twiceBlockEntry (D.n D.m - 1) p := by
  rw [weightY_eq_weightX_add, mul_add, two_mul_weightX, twiceBlockEntry_n_sub_one,
    ← D.sortedParamY_sub_paramX τ p]
  ring

/-- The columns of height `u` that keep their height under branching are at most as many as all
columns of height `u` at `τ`. With `μ = μ(X_m)`, `μ' = μ(Y_m)` and `u = p + 1 < n_m` this is
`μ'_p - μ_{p+1} ≤ μ_p - μ_{p+1}`. Together with `μ_{p+1} ≤ μ'_p` (`weightY_eq_weightX_add`) it says
that the weights interlace. -/
lemma keptColumns_le_columnCount (τ : D.Φ) (u : ℕ) : D.keptColumns u ≤ D.columnCount τ u := by
  have h_gap : D.k + D.t + 1 ≤ D.halfGap := D.k_add_t_add_one_le_halfGap
  have h_weight : D.liftWeight 1 τ = D.liftWeight 0 τ + 2 * D.halfGap := D.liftWeight_succ 0 τ
  grind [keptColumns, columnCount, reducedHalfGap, Data.gap, D.one_lt_k]

/-- No column of height `u < k` keeps its height under branching, where `k = D.k` is the rank of
`X_0`. -/
lemma keptColumns_eq_zero_of_lt_k {u : ℕ} (hu : u < D.k) : D.keptColumns u = 0 :=
  ite_eq_right fun h_block ↦ hu.not_ge h_block.1

/-- With `m = D.m` and `n_m = D.n D.m`, `D.keptColumns (n_m - 1) = 0`: no column of height `n_m - 1`
of the weight on `X_m` keeps its height under branching to `Y_m`. Hence the weights `μ(X_m)` and
`μ(Y_m)` have the same last entry. -/
lemma keptColumns_n_sub_one : D.keptColumns (D.n D.m - 1) = 0 := by
  obtain ⟨l, hl⟩ : ∃ l : ℕ, D.m = l + 1 :=
    Nat.exists_eq_add_one.2 (by linarith [D.ten_thousand_le_m])
  obtain ⟨s, hs⟩ : Odd D.t := D.t_odd
  have h_rank : D.n (l + 1) = D.n l + (D.t + 1) := D.n_succ l
  have h_between : D.n D.m - 1 ∈ Ioo (D.n l) (D.n (l + 1)) := by
    rw [hl, mem_Ioo]
    omega
  exact ite_eq_right fun h_block ↦ D.not_dvd_sub_k l h_between h_block.2

/-- For `u ≤ N`, the sum of `D.columnsY τ v` over heights `u ≤ v < N`, plus `D.keptColumns N`,
equals the sum of `D.columnCount τ v` over `u < v ≤ N`, plus `D.keptColumns u`. The `keptColumns`
terms telescope. -/
lemma sum_columnsY_add_keptColumns (τ : D.Φ) {u N : ℕ} (hN : u ≤ N) :
    ∑ v ∈ Ico u N, D.columnsY τ v + D.keptColumns N =
      ∑ v ∈ Ico (u + 1) (N + 1), D.columnCount τ v + D.keptColumns u := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
    rw [sum_Ico_succ_top hN, sum_Ico_succ_top (Nat.add_le_add_right hN 1), columnsY]
    grind [D.keptColumns_le_columnCount τ (N + 1)]

/-- The weight `μ(Y_m) = D.weightY τ` at `τ` has `D.columnsY τ u` columns of each height
`u < n_m - 1`, and its last entry is `D.lastEntry D.m τ`, the last entry of `μ(X_m)`: for
`p < n_m - 1` the entry `p` is the last entry plus the number of columns of height above `p`. -/
lemma weightY_eq (τ : D.Φ) {p : ℕ} (hp : p < D.n D.m - 1) :
    D.weightY τ p = D.lastEntry D.m τ + (∑ u ∈ Ioo p (D.n D.m - 1), D.columnsY τ u : ℕ) := by
  have h_telescope : ∑ u ∈ Ioo p (D.n D.m - 1), D.columnsY τ u =
      ∑ u ∈ Ioo (p + 1) (D.n D.m), D.columnCount τ u + D.keptColumns (p + 1) := by
    simpa only [keptColumns_n_sub_one, Nat.sub_add_cancel (D.n_pos D.m), Ico_add_one_left_eq_Ioo,
      add_zero] using D.sum_columnsY_add_keptColumns τ (u := p + 1) hp
  rw [weightY_eq_weightX_add, D.weightX_eq D.m τ (Nat.add_lt_of_lt_sub hp), h_telescope,
    Nat.cast_add, add_assoc]

/-- At most `Δ / 2 = D.halfGap` columns of each height keep their height under branching. -/
lemma keptColumns_le_halfGap (u : ℕ) : D.keptColumns u ≤ D.halfGap := by
  grind [keptColumns, reducedHalfGap]

/-- At most `Δ / 2 = D.halfGap` columns of each height `u > k` lose a box under branching. -/
lemma columnCount_sub_keptColumns_le_halfGap (τ : D.Φ) {u : ℕ} (hu : D.k < u) :
    D.columnCount τ u - D.keptColumns u ≤ D.halfGap := by
  grind [keptColumns, columnCount, reducedHalfGap, Data.gap, D.one_lt_k]

/-- The weight `μ(Y_m)` at `τ` has at most `Δ = D.gap` columns of each height `u ≥ k`. -/
lemma columnsY_le (τ : D.Φ) {u : ℕ} (hu : D.k ≤ u) : D.columnsY τ u ≤ D.gap := by
  rw [columnsY, Data.gap, two_mul]
  exact add_le_add (D.keptColumns_le_halfGap u)
    (D.columnCount_sub_keptColumns_le_halfGap τ (Nat.lt_succ_of_le hu))

/-! ### The exponent of the branching map -/

/-- The number `n_τ = |μ(X_m)_τ| - |μ(Y_m)_τ|`, where `|μ|` is the sum of the entries of `μ`. -/
def branchExponent (τ : D.Φ) : ℤ :=
  ∑ p ∈ range (D.n D.m), D.weightX D.m τ p - ∑ p ∈ range (D.n D.m - 1), D.weightY τ p

/-- The first `n_j = D.n j` entries of `D.paramX τ` are twice the Harish-Chandra parameter of `X_j`
at `τ`. Their sum is twice `a_τ - (t + 1) (κ_1 + ⋯ + κ_j)`. -/
lemma sum_paramX (j : ℕ) (τ : D.Φ) :
    ∑ p ∈ range (D.n j), D.paramX τ p =
      2 * D.firstRowExcess τ - 2 * (D.t + 1) * ∑ i ∈ range j, (D.liftWeight (i + 1) τ : ℤ) := by
  induction j with
  | zero =>
    have h_head (p : ℕ) (hp : p ∈ range D.k) : D.paramX τ p =
        twiceBlockEntry D.k p + if p = 0 then 2 * (D.firstRowExcess τ : ℤ) else 0 :=
      ite_eq_left (mem_range.1 hp)
    simp [n_zero, sum_congr rfl h_head, sum_add_distrib, sum_twiceBlockEntry, D.k_pos]
  | succ j ih =>
    have h_block : ∑ b ∈ range (D.t + 1), D.paramX τ (D.n j + b) =
        -2 * (D.t + 1) * D.liftWeight (j + 1) τ := by
      rw [sum_congr rfl fun b hb ↦ D.paramX_block j τ (mem_range.1 hb), sum_sub_distrib,
        sum_twiceBlockEntry, sum_const, card_range, nsmul_eq_mul]
      push_cast
      ring
    rw [n_succ, sum_range_add, ih, h_block, sum_range_succ]
    ring

/-- The first `n_m - 1` entries of `D.sortedParamY τ` are twice the Harish-Chandra parameter of the
definite space `Y_m` at the place `τ`, in decreasing order. For each `j`, the sum of the first
`n_j - 1` entries is twice `-(κ_{1/2} + ⋯ + κ_{j - 1/2}) - t (κ_1 + ⋯ + κ_j)`. The case `j = m` is
twice the sum of the entries of the parameter of `Y_m`. -/
lemma sum_sortedParamY (j : ℕ) (τ : D.Φ) :
    ∑ p ∈ range (D.n j - 1), D.sortedParamY τ p =
      -2 * ∑ i ∈ range j, (D.liftWeight (i + 1) τ - D.halfGap : ℤ) -
        2 * D.t * ∑ i ∈ range j, (D.liftWeight (i + 1) τ : ℤ) := by
  induction j with
  | zero =>
    have h_head (p : ℕ) (hp : p ∈ range (D.k - 1)) :
        D.sortedParamY τ p = twiceBlockEntry (D.k - 1) p := by
      have hp_lt : p + 1 < D.k := Nat.add_lt_of_lt_sub (mem_range.1 hp)
      rw [sortedParamY, ite_eq_left hp_lt, D.two_mul_targetParameter_of_lt τ hp_lt]
    simp [n_zero, sum_congr rfl h_head, sum_twiceBlockEntry]
  | succ j ih =>
    have h_rank : D.n (j + 1) - 1 = D.n j + D.t := by rw [n_succ, ← add_assoc, Nat.add_sub_cancel]
    have h_first : ∑ p ∈ range (D.n j), D.sortedParamY τ p =
        ∑ p ∈ range (D.n j - 1), D.sortedParamY τ p + D.sortedParamY τ (D.n j - 1) := by
      rw [← sum_range_succ, Nat.sub_add_cancel (D.n_pos j)]
    have h_block : ∑ b ∈ range D.t, D.sortedParamY τ (D.n j + b) =
        -2 * D.t * D.liftWeight (j + 1) τ := by
      rw [sum_congr rfl fun b hb ↦ D.sortedParamY_block j τ (mem_range.1 hb), sum_sub_distrib,
        sum_twiceBlockEntry, sum_const, card_range, nsmul_eq_mul]
      ring
    rw [h_rank, sum_range_add, h_first, ih, sortedParamY_n_sub_one, targetParameter_k_sub_one_add,
      h_block, sum_range_succ, sum_range_succ]
    ring

/-- The exponent `n_τ = |μ(X_m)_τ| - |μ(Y_m)_τ|`, where `|μ|` is the sum of the entries of the
weight `μ`, equals `a_τ - m Δ / 2`. -/
lemma branchExponent_eq (τ : D.Φ) : D.branchExponent τ = D.firstRowExcess τ - D.m * D.halfGap := by
  -- The blocks have sum `0`, so `n_τ` is the difference of the sums of the parameters.
  have h_params : 2 * D.branchExponent τ = ∑ p ∈ range (D.n D.m), D.paramX τ p -
      ∑ p ∈ range (D.n D.m - 1), D.sortedParamY τ p := by
    simp only [branchExponent, mul_sub, mul_sum, two_mul_weightX, two_mul_weightY, sum_sub_distrib,
      sum_twiceBlockEntry, sub_zero]
  rw [sum_paramX, sum_sortedParamY, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
    at h_params
  linarith

/-- Let `|μ|` be the sum of the entries of a weight `μ`. The exponent
`n_τ = |μ(X_m)_τ| - |μ(Y_m)_τ|` is the number of columns of `μ(X_m)` that lose a box under branching
to `Y_m`, plus the last entry of `μ(X_m)`. Of the `D.columnCount τ u` columns of height
`u < n_m = D.n D.m`, all but `D.keptColumns u` lose a box. This is the form of the exponent in
`New.exists_branching_matrix`. -/
lemma branchExponent_eq_sum_columns (τ : D.Φ) :
    D.branchExponent τ =
      (∑ u ∈ Ioo 0 (D.n D.m), (D.columnCount τ u - D.keptColumns u) : ℕ) + D.lastEntry D.m τ := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, D.n D.m = N + 1 := Nat.exists_eq_add_one.2 (D.n_pos D.m)
  -- Pair entry `p` of `μ(Y_m)` with entry `p + 1` of `μ(X_m)`; entry `0` of `μ(X_m)` is left over.
  have h_pair : D.branchExponent τ =
      D.weightX D.m τ 0 - ∑ p ∈ range N, (D.keptColumns (p + 1) : ℤ) := by
    simp [branchExponent, hN, sum_range_succ', weightY_eq_weightX_add, sum_add_distrib]
  have h_shift : ∑ p ∈ range N, (D.keptColumns (p + 1) : ℤ) =
      ∑ u ∈ Ioo 0 (D.n D.m), (D.keptColumns u : ℤ) := by
    rw [hN, ← Ico_add_one_left_eq_Ioo, ← sum_Ico_add', range_eq_Ico]
  push_cast [h_pair, h_shift, D.weightX_eq D.m τ (D.n_pos D.m), D.keptColumns_le_columnCount τ,
    sum_sub_distrib]
  ring

/-- The sum of the exponents `n_τ` over the `f` infinite places of `E` is `#Φ_a · a - f m Δ / 2`,
where `Φ_a = D.aPlaces` is the set of `a`-places and `Δ / 2 = D.halfGap`. -/
lemma sum_branchExponent :
    (∑ τ : D.Φ, D.branchExponent τ : ℝ) = #D.aPlaces * D.a - D.f * (D.m * D.halfGap) := by
  simp [branchExponent_eq, firstRowExcess, sum_sub_distrib]

end Data

end New

end Diagrams

end
