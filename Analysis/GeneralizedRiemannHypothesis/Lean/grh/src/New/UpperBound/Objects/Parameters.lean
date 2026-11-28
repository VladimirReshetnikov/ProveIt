import Lib.Weil.Lift
import New.UpperBound.Objects.InsertBlock
import New.UpperBound.Objects.LabelsAndIndexTypes

/-!
# Index sets, signs and parameters of the grids; the parameters of every step correspond

Two grids of unitary groups, `Y` and `Ỹ`, with nodes `(i, j)`, are treated together by a flag `z`
(`false` for `Y`, `true` for `Ỹ`). A node has a base block of `r` (in `Ỹ`, `r + 1`) indices, `i`
added blocks of one kind and `j` of another (`New.BlockIndex`). For `z = false` the node `(i, j)` is
`Y^i_j` with its parameter. For `z = true` it is `Ỹ^j_i` with the negative of its parameter, so that
one formula serves both grids. An offset `o` shifts the second kind of block; the grids have
`o = 0`, and the nodes with `i = 0` are the intervals `[o + 1, o + j]` of the triangles.

* `New.Data.GridIndex`, `New.Data.gridSigns`, `New.Data.gridParam`: index set, signs and doubled
  parameter of a node.
* `New.Data.gridDiagEquiv`: at `(j, j)`, `j ≤ m`, `Ỹ` is `Y` plus one vector of sign `(-1)^j`.
* `New.Data.gridParam_interlace`: at the node `(m, m)` the parameter of `Y` and that of `Ỹ`
  (`-gridParam true`) interlace.
* `New.Data.gridCentres`, `New.Data.isParam_gridParam`: the parameter of a node consists of a stem
  and the blocks of a set of centres (`New.CentreSystem`).
* `New.Data.paramsCorrespond_grid_succ_left`, `New.Data.paramsCorrespond_grid_succ_right`,
  `New.Data.paramsCorrespond_leftPair`: each step inserts a block, so the parameters correspond
  (`New.ParamsCorrespond`).

Notions from other files:
* `New.Data`: the admissible data `D`, with `m` (even) lifts, the rank `r` (odd), `k = r + 1 - m`,
  `t = 5 r`, the gap `Δ = D.gap = 2 halfGap` and the set `D.Φ` of infinite places.
* `New.Data.RowIndex`: an index set with `r` elements, numbered by `New.Data.basisNumber`.
* `New.Data.liftWeight`: the centre `w_j = κ_j = κ + (j + 1/2) Δ` at an infinite place, with
  `κ = D.weight`, the gap `Δ = D.gap` and `Δ / 2 = D.halfGap`.
* `New.Data.targetParameter`: the target parameter, the vector
  `λ^Y = ([k - 1]; -κ_{1/2}, -κ_{3/2}, …)`, with entries numbered from `0`; the entry `r` is
  `-κ_{m+1/2}`.
* `New.ParamsCorrespond γ γ' l l' s s'`: at each infinite place, the doubled parameters `l` (signs
  `s`) and `l'` (signs `s'`) satisfy the block rule (`New.IsBlockRule`) for the weights `γ`, `γ'`.
-/

noncomputable section

namespace New.Data

open Fintype Function Finset BlockIndex Exchange

section Nodes

variable {j : ℕ} {P : Parameters} (D : Data P) (z : Bool) (o i : ℕ) (τ : D.Φ)

/-- The index set of the node `(i, j)`. For `z = false` (grid `Y`) it is `D.RowIndex` with `i`
and then `j` blocks of length `t`. For `z = true` (grid `Ỹ`) it is `D.RowIndex ⊕ Unit` with `i`
blocks of length `t + 1` and `j` blocks of length `t - 1`. -/
protected def GridIndex (j : ℕ) : Type :=
  BlockIndex (BlockIndex (BlockIndex D.RowIndex Unit z.toNat) (Fin (D.t + z.toNat)) i)
    (Fin (D.t - z.toNat)) j
  deriving Fintype, DecidableEq

lemma gridIndex_false (j : ℕ) :
    D.GridIndex false i j = BlockIndex (BlockIndex D.RowIndex (Fin D.t) i) (Fin D.t) j := rfl

/-- The index set `D.GridIndex true i j` of the node `(i, j)` of grid `Ỹ` is `D.RowIndex ⊕ Unit`
with `i` blocks `Fin (D.t + 1)` and then `j` blocks `Fin (D.t - 1)`. -/
lemma gridIndex_true (j : ℕ) : D.GridIndex true i j =
    BlockIndex (BlockIndex (D.RowIndex ⊕ Unit) (Fin (D.t + 1)) i) (Fin (D.t - 1)) j := rfl

/-- The numbering of the base index set: `D.basisNumber` on `D.RowIndex`, and `r` for the extra
point of grid `Ỹ`. -/
def gridNumber : ∀ z : Bool, BlockIndex D.RowIndex Unit z.toNat ≃ Fin (D.r + z.toNat)
  | false => D.basisNumber
  | true => (D.basisNumber.sumCongr finOneEquiv.symm).trans finSumFinEquiv

/-- A chosen splitting of the index set of the node `(i, j)` into blocks. An index becomes either a
base number or a pair `(l, b)` of a block of the first or second kind and a position in that block.
At the node `(0, 0)` the base number is the one under `D.gridNumber z`; otherwise the bijection is
arbitrary (`New.BlockIndex.equivSum`). -/
def gridBlockEquiv {z : Bool} {i : ℕ} : D.GridIndex z i j ≃
    (Fin (D.r + z.toNat) ⊕ Fin i × Fin (D.t + z.toNat)) ⊕ Fin j × Fin (D.t - z.toNat) :=
  equivSum (equivSum (D.gridNumber z) i) j

/-- The sign `entrySign o j a` is `-1` if `o + a + min (a - o) j` is odd and `1` otherwise, the
subtraction being truncated at `0`. -/
lemma entrySign_eq_ite (j a : ℕ) :
    entrySign o j a = (if (o + a + min (a - o) j) % 2 = 1 then -1 else 1) := by
  grind [entrySign_eq_neg_one_pow, neg_one_pow_eq_ite]

/-- The signs at the node `(i, j)` with offset `o`; the grids are the case `o = 0`, the triangles
the case `i = 0`. The base index with number `n` has the sign `entrySign o j (n + 1 - k)`, and the
added blocks have the sign `+1`. -/
def gridSigns (j : ℕ) (x : D.GridIndex z i j) : ℤˣ :=
  (D.gridBlockEquiv x).elim
    (Sum.elim (fun n : Fin (D.r + z.toNat) ↦ entrySign o j (n.val + 1 - D.k)) 1) 1

/-- The doubled parameter at the node `(i, j)` with offset `o` and the infinite place `τ`: an
integer vector on the index set (`HCParam`). For `o = 0` it is twice the
parameter of `Y^i_j` if `z = false`, and minus twice the parameter of `Ỹ^j_i` if `z = true`; see
`gridParam_false` and `neg_gridParam_true`. A block of length `s` centred at `c` has the doubled
entries `2c + s - 1, 2c + s - 3, …, 2c - s + 1`. -/
def gridParam (j : ℕ) (τ : D.Φ) : HCParam (D.gridSigns z o i j) := fun x : D.GridIndex z i j ↦
  let y : ℤ := (D.gridBlockEquiv x).elim
    (Sum.elim (fun n : Fin (D.r + z.toNat) ↦ 2 * D.targetParameter τ n.val)
      fun (l, b) ↦ 2 * D.liftWeight (l + 1) τ + D.t - 1 - 2 * b)
    fun (l, b) ↦ D.t - 1 - 2 * (D.liftWeight (l + 1 + o) τ + z.toNat) - 2 * b
  bif z then y + 1 else if (j + i) % 2 = 1 then y - 1 else y

/-- Grid `Y`: `D.gridParam false o i j τ` is twice `D.targetParameter τ` on the base, with blocks of
length `t` centred at `w_l` (`1 ≤ l ≤ i`) and at `-w_(o+l)` (`1 ≤ l ≤ j`). All entries are lowered
by `1` if `i + j` is odd. -/
lemma gridParam_false (x : D.GridIndex false i j) :
    D.gridParam false o i j τ x =
      (D.gridBlockEquiv x).elim
        (Sum.elim (fun n : Fin (D.r + false.toNat) ↦ 2 * D.targetParameter τ n.val)
          fun (l, b) ↦ (2 * D.liftWeight (l + 1) τ + D.t - 1 - 2 * b : ℤ))
        (fun (l, b) ↦ (-2 * D.liftWeight (l + 1 + o) τ + D.t - 1 - 2 * b : ℤ)) -
      (if (j + i) % 2 = 1 then 1 else 0) := by
  rw [gridParam, Bool.cond_false]
  rcases D.gridBlockEquiv x with (n | ⟨l, b⟩) | ⟨l, b⟩ <;> grind

/-- Grid `Ỹ`: `D.gridParam true o i j τ` is twice `D.targetParameter τ`, plus `1`, on the base, with
blocks of length `t + 1` centred at `w_l` (`1 ≤ l ≤ i`) and blocks of length `t - 1` centred at
`-w_(o+l)` (`1 ≤ l ≤ j`). -/
lemma gridParam_true (x : D.GridIndex true i j) :
    D.gridParam true o i j τ x =
      (D.gridBlockEquiv x).elim
        (Sum.elim (fun n : Fin (D.r + true.toNat) ↦ 2 * D.targetParameter τ n.val + 1)
          fun (l, b) ↦ (2 * D.liftWeight (l + 1) τ + (D.t + 1) - 1 - 2 * b : ℤ))
        fun (l, b) ↦ (-2 * D.liftWeight (l + 1 + o) τ + (D.t - 1) - 1 - 2 * b : ℤ) := by
  rw [gridParam, Bool.cond_true]
  rcases D.gridBlockEquiv x with (n | ⟨l, b⟩) | ⟨l, b⟩ <;> grind

/-- The doubled parameter of `Ỹ^j_i` is minus `gridParam true 0 i j`, entry by entry: minus twice
`D.targetParameter τ`, minus `1`, on the base, and rising blocks of length `t + 1` centred at `-w_l`
(`1 ≤ l ≤ i`) and of length `t - 1` centred at `w_l` (`1 ≤ l ≤ j`). -/
lemma neg_gridParam_true (x : D.GridIndex true i j) :
    (-D.gridParam true 0 i j τ) x =
      (D.gridBlockEquiv x).elim
        (Sum.elim (fun n : Fin (D.r + true.toNat) ↦ -(2 * D.targetParameter τ n.val) - 1)
          fun (l, b) ↦ (-2 * D.liftWeight (l + 1) τ - (D.t + 1) + 1 + 2 * b : ℤ))
        fun (l, b) ↦ (2 * D.liftWeight (l + 1) τ - (D.t - 1) + 1 + 2 * b : ℤ) := by
  rw [Pi.neg_apply, gridParam_true]
  rcases D.gridBlockEquiv x with (n | ⟨l, b⟩) | ⟨l, b⟩ <;> grind

/-- The signs of the space `Y_j` on its index type `D.Y j` (`D.RowIndex` and `j` blocks of length
`t`), which is the node `(0, j)` of grid `Y` with offset `0`. -/
def signsY (j : ℕ) : D.Y j → ℤˣ := D.gridSigns false 0 0 j

/-- Twice the parameter of the space `Y_j` at each infinite place, on the index type `D.Y j`
(`D.RowIndex` and `j` blocks of length `t`): the node `(0, j)` of grid `Y` with offset `0`. -/
def paramY (j : ℕ) : D.Φ → D.Y j → ℤ := D.gridParam false 0 0 j

variable {z o i}

/-- A step between two nodes inserts the block of a centre `±w_{l+1}`, and each of the two nodes has
a weight: if its index type `n` has cardinality `N`, the weight at `τ` is `⌊N/2⌋ - w_{l+1}(τ)` for
`c = true` and `⌈N/2⌉ - w_{l+1}(τ)` for `c = false`. The ceiling is written `(N + 1) / 2`. -/
def gridWeight (c : Bool) (l : ℕ) (n : Type) [Fintype n] (τ : D.Φ) : ℤ :=
  (((Fintype.card n + (!c).toNat) / 2 : ℕ) - D.liftWeight (l + 1) τ : ℤ)

/-- The product over the infinite places of the field `D.E` of the chosen joint harmonic
polynomials (`New.jointHarmonic`) for the nodes `(a, b)` and `(i, j)` of grid `z` with offset `o`.
The weights are `D.gridWeight c l`, where `l` gives the centre `±w_{l+1}` of the step and `c` the
rounding. The parameters are negated (`negIf`) if `d` is true, as for the step from `(i, j)` to
`(i + 1, j)` (see `paramsCorrespond_grid`). -/
def gridHarmonic (o : ℕ) (d c : Bool) (l : ℕ) (z : Bool) (a b i j : ℕ) :
    MvPolynomial (NumberField.InfinitePlace D.E × D.GridIndex z i j × D.GridIndex z a b) ℂ :=
  jointHarmonic (D.gridWeight c l (D.GridIndex z a b)) (D.gridWeight c l (D.GridIndex z i j))
    (negIf d (D.gridParam z o a b)) (negIf d (D.gridParam z o i j)) (D.gridSigns z o a b)
    (D.gridSigns z o i j)

/-! ### Ranks and numbers of negative signs -/

/-- The node `(i, j)` has rank `r + i t + j t` in grid `Y`, and `r + 1 + i (t + 1) + j (t - 1)` in
grid `Ỹ`, where it is the space `Ỹ^j_i`. -/
lemma card_gridIndex : Fintype.card (D.GridIndex z i j) =
    D.r + z.toNat + i * (D.t + z.toNat) + j * (D.t - z.toNat) := by
  simp [card_congr D.gridBlockEquiv]

/-- The negative signs of the node `(i, j)` with offset `o` all lie on the base, so their number
is that of the `n < r + z` with `entrySign o j (n + 1 - k) = -1`. -/
lemma negCount_gridSigns_eq_sum : negCount (D.gridSigns z o i j) =
    ∑ n ∈ range (D.r + z.toNat), (if (entrySign o j (n + 1 - D.k) = -1) then 1 else 0) := by
  rw [negCount, Fintype.card_subtype, card_filter, ← D.gridBlockEquiv.symm.sum_comp, sum_range]
  -- the added blocks have the sign `+1` and contribute nothing
  simp [gridSigns, -sum_boole]
  rfl

/-- With offset `0`, the node `(i, j)` has `⌊(m - j)/2⌋` negative signs in grid `Y` and
`⌊(m - j + 1)/2⌋` in grid `Ỹ` (the space `Ỹ^j_i`), where `m - j` is truncated at `0`. -/
lemma negCount_gridSigns (z : Bool) (i j : ℕ) :
    negCount (D.gridSigns z 0 i j) = (D.m - j + z.toNat) / 2 := by
  -- `entrySign 0 j a = -1` exactly for `a = j + 1, j + 3, …`
  have h_count (N : ℕ) : ∑ n ∈ range N, (if entrySign 0 j (n + 1 - D.k) = -1 then 1 else 0) =
      (N + 1 - D.k - j) / 2 := by
    induction N with
    | zero => grind [sum_range_zero]
    | succ N ih => grind [entrySign_eq_ite, units_ne_neg_self, sum_range_succ]
  rw [negCount_gridSigns_eq_sum, h_count]
  grind [Bool, D.r_add_one]

/-- With offset `0`, the signs of grid `Ỹ` at the node `(0, 0)` are those of `D.Y 0` (`D.signsY 0`),
with the sign `+1` at the extra point. -/
lemma gridSigns_true_zero : D.gridSigns true 0 0 0 = Sum.elim (D.signsY 0) 1 := by
  ext1 (x | x)
  · rfl
  · -- the extra point has the number `r`, and `r + 1 - k = m` is even
    change entrySign 0 0 (D.r + (finOneEquiv.symm x : ℕ) + 1 - D.k) = 1
    simp [entrySign_eq_ite, show (D.r + 1 - D.k) % 2 = 0 by grind]

/-- On the diagonal, with offset `0`, the signs of `Ỹ` are, up to a bijection of the index types,
the signs of `Y` together with one more sign `(-1) ^ min j m`. -/
lemma exists_equiv_diagonal_signs (j : ℕ) :
    ∃ e : D.GridIndex true j j ≃ D.GridIndex false j j ⊕ Unit,
      Sum.elim (D.gridSigns false 0 j j) (fun _ : Unit ↦ (-1) ^ min j D.m) ∘ e =
        D.gridSigns true 0 j j := by
  -- It suffices to compare the cardinalities and the numbers of negative signs.
  have h_card :
      Fintype.card (D.GridIndex true j j) = Fintype.card (D.GridIndex false j j ⊕ Unit) := by
    have h_blocks : j * (D.t + 1) + j * (D.t - 1) = j * D.t + j * D.t := by
      zify [D.t_odd.pos]
      ring
    simp only [card_sum, card_unit, card_gridIndex, Bool.toNat_true, Bool.toNat_false, add_zero,
      tsub_zero]
    omega
  -- the extra point counts as negative exactly when `min j m` is odd
  have h_extra : negCount (fun _ : Unit ↦ (-1) ^ min j D.m) = min j D.m % 2 := by
    rcases Nat.even_or_odd (min j D.m) with h_even | h_odd
    · simp [negCount, h_even.neg_one_pow, Nat.even_iff.1 h_even]
    · simp [negCount, h_odd.neg_one_pow, Nat.odd_iff.1 h_odd]
  have h_neg : negCount (D.gridSigns true 0 j j) =
      negCount (Sum.elim (D.gridSigns false 0 j j) fun _ : Unit ↦ (-1) ^ min j D.m) := by
    rw [negCount_sumElim, negCount_gridSigns, negCount_gridSigns, h_extra]
    grind
  exact exists_equiv_comp_eq_of_negCount_eq h_card h_neg

/-- A bijection from the index set of `Y` at `(j, j)` plus one point to that of `Ỹ`. It is the
identity for `j = 0`. Otherwise it is chosen to match the signs (`exists_equiv_diagonal_signs`). -/
def gridDiagEquiv : ∀ j : ℕ, D.GridIndex false j j ⊕ Unit ≃ D.GridIndex true j j
  | 0 => Equiv.refl (D.GridIndex false 0 0 ⊕ Unit)
  | j + 1 => (D.exists_equiv_diagonal_signs (j + 1)).choose.symm

/-- For `j ≤ m` and offset `0`, the signs of `Ỹ` at `(j, j)` are, through `D.gridDiagEquiv j`,
those of `Y` together with the sign `(-1)^j` at the extra point. -/
lemma sumElim_gridSigns_comp_gridDiagEquiv_symm (hj : j ≤ D.m) :
    Sum.elim (D.gridSigns false 0 j j) (fun _ : Unit ↦ (-1) ^ j) ∘ (D.gridDiagEquiv j).symm =
      D.gridSigns true 0 j j := by
  cases j with
  | zero => exact D.gridSigns_true_zero.symm
  | succ j =>
    rw [gridDiagEquiv, Equiv.symm_symm]
    simpa only [min_eq_left hj] using (D.exists_equiv_diagonal_signs (j + 1)).choose_spec

/-! ### Gaps, interlacing and sizes of the parameters -/

/-- The parity of the size of the index set `D.GridIndex z i j` of the node `(i, j)`: it is even in
grid `Ỹ` (`z = true`), and in grid `Y` (`z = false`) it is odd iff `i + j` is even. -/
lemma card_gridIndex_mod_two (z : Bool) (i j : ℕ) :
    Fintype.card (D.GridIndex z i j) % 2 = (if z then 0 else (i + j + 1) % 2) := by
  -- each added block has odd length in grid `Y` and even length in grid `Ỹ`
  rw [card_gridIndex]
  induction i with
  | zero => induction j <;> grind [D.r_odd, D.t_odd]
  | succ i ih => grind [D.t_odd]

/-- The weights `D.liftWeight a τ` increase by at least `D.gap` from `a` to any `b > a`, and by at
least `2 * D.gap` if `b > a + 1`. -/
lemma liftWeight_add_gap_le (a b : ℕ) (hab : a < b) :
    D.liftWeight a τ + (if a + 1 < b then 2 else 1) * D.gap ≤ D.liftWeight b τ := by
  have h_succ (c : ℕ) : D.liftWeight (c + 1) τ = D.liftWeight c τ + D.gap := by grind
  induction hab with
  | refl => simp [h_succ]
  | step hab ih => grind

local grind_pattern liftWeight_add_gap_le => D.liftWeight a τ, D.liftWeight b τ

/-- For `m ≤ j` and offset `0`, all signs at the node `(i, j)` are `+1`. -/
lemma gridSigns_eq_one (hj : D.m ≤ j) : D.gridSigns z 0 i j = 1 := by
  funext x
  rw [gridSigns]
  rcases D.gridBlockEquiv x with (⟨n, hn⟩ | y) | y
  · -- here `n + 1 - k ≤ m ≤ j`, so the exponent of `-1` is `2 (n + 1 - k)`
    have h_le : n + 1 - D.k ≤ j := by grind [Bool]
    simp [entrySign_eq_neg_one_pow, h_le, ← two_mul]
  all_goals rfl

/-- The number of entries above `x` of the falling block `A, A - 2, …` of length `n` is
`⌊(A + 1 - x) / 2⌋`, clamped to the interval `[0, n]`. -/
lemma sum_ite_lt_sub_two_mul (x A : ℤ) (n : ℕ) :
    ∑ b : Fin n, (if x < A - 2 * b then 1 else 0 : ℤ) = max 0 (min (n : ℤ) ((A + 1 - x) / 2)) := by
  induction n with
  | zero => simp
  | succ n ih => grind [Fin.sum_univ_castSucc]

/-- The number of entries above `x` of the rising block `A, A + 2, …` of length `n` is
`⌊(A + 2 n - 1 - x) / 2⌋`, clamped to the interval `[0, n]`. -/
lemma sum_ite_lt_add_two_mul (x A : ℤ) (n : ℕ) :
    ∑ b : Fin n, (if x < A + 2 * b then 1 else 0 : ℤ) =
      max 0 (min (n : ℤ) ((A + 2 * n - 1 - x) / 2)) := by
  induction n with
  | zero => simp
  | succ n ih => grind [Fin.sum_univ_castSucc]

/-- Two blocks with step `2` and the same centre `c`, of lengths `n + 1` and `n`, interlace. The
left side is the number of entries above `x` of the longer block, less that of the shorter one. It
is `1` if `x` is below an integer `low ≤ c - n`, it is `0` if `x` is not below an integer
`high ≥ c + n`, and it is always `0` or `1`. -/
lemma max_min_succ_sub_max_min_mem_Icc (x : ℤ) {n c low high : ℤ} (hn : 0 ≤ n)
    (h_low : low ≤ c - n) (h_high : c + n ≤ high) :
    max 0 (min (n + 1) ((c + n + 1 - x) / 2)) - max 0 (min n ((c + n - x) / 2)) ∈
      Icc (if x < low then 1 else 0 : ℤ) (if x < high then 1 else 0) := by
  grind

/-- The entry `D.k - 1 + a` of `D.targetParameter τ` is `D.halfGap - D.liftWeight (a + 1) τ`. -/
lemma targetParameter_sub_one_add (a : ℕ) :
    D.targetParameter τ (D.k - 1 + a) = D.halfGap - D.liftWeight (a + 1) τ := by
  grind [targetParameter_eq, D.k_pos]

/-- The base case of `gridParam_interlace`. Let `λ_n = D.targetParameter τ n` be the entries of the
target parameter and `s = 2 λ_(k-1)`. The number of `n < k` with `x < -2 λ_n - 1`, less the number
of `n < k - 1` with `x < 2 λ_n`, is `1` if `x < s`, is `0` if `-s - 1 ≤ x`, and is always `0` or
`1`. -/
lemma sum_ite_targetParameter_sub_sum_ite_mem_Icc (x : ℤ) :
    ∑ n ∈ range (D.k - 1 + 1), (if x < -(2 * D.targetParameter τ n) - 1 then 1 else 0 : ℤ) -
        ∑ n ∈ range (D.k - 1), (if x < 2 * D.targetParameter τ n then 1 else 0 : ℤ) ∈
      Icc (if x < 2 * D.targetParameter τ (D.k - 1) then 1 else 0 : ℤ)
        (if x < -(2 * D.targetParameter τ (D.k - 1)) - 1 then 1 else 0) := by
  -- The first `k - 1` entries of twice the target parameter form the block `k - 2, k - 4, …`.
  have h_k : D.k % 2 = 0 := Nat.even_iff.1 D.k_even
  have h_falling (n : Fin (D.k - 1)) : 2 * D.targetParameter τ n = D.k - 2 - 2 * n := by
    rw [targetParameter_eq, ite_eq_left (by omega)]
    omega
  have h_rising (n : Fin (D.k - 1)) : -(D.k - 2 - 2 * n : ℤ) - 1 = 1 - D.k + 2 * n := by ring
  -- The next entry lies far below this block.
  have h_next : D.targetParameter τ (D.k - 1) = D.halfGap - D.liftWeight 1 τ :=
    D.targetParameter_sub_one_add τ 0
  have h_centre : D.gap ≤ D.liftWeight 1 τ := D.nat_le_of_hasLogBound
  have h_sizes : D.k + D.t + 1 ≤ D.halfGap := D.k_add_t_add_one_le_halfGap
  have h_gap : D.gap = 2 * D.halfGap := rfl
  rw [sum_range_succ, sum_range, sum_range, mem_Icc]
  simp only [h_falling, h_rising, sum_ite_lt_sub_two_mul, sum_ite_lt_add_two_mul, h_next]
  omega

/-- At the infinite place `τ` and with offset `0`, the entries of the parameters of the node
`(m, m)` of grid `Ỹ` (doubled, these are `-gridParam true`) and of grid `Y` (flag `false`)
alternate in decreasing order, the
first coming from `Ỹ`: for every integer `x`, the number of doubled entries above `x` on `Ỹ^m_m`,
less that on `Y^m_m`, is `0` or `1`. -/
lemma gridParam_interlace (x : ℤ) :
    (#{y' : D.GridIndex true D.m D.m | x < -D.gridParam true 0 D.m D.m τ y'} -
      #{y : D.GridIndex false D.m D.m | x < D.gridParam false 0 D.m D.m τ y} : ℤ) ∈ Icc 0 1 := by
  -- Count with the indicator `φ` of `x < y`, block by block. The difference lies between `φ s` and
  -- `φ (-s - 1)` for `s` twice the entry `r` of the target parameter; this sharper bound allows
  -- induction on `m`.
  have h_rank : D.r = D.k - 1 + D.m := by grind [D.r_add_one, D.k_pos]
  let φ (y : ℤ) : ℤ := if x < y then 1 else 0
  -- `g n y` is `⌊(y - x) / 2⌋` clamped to the interval `[0, n]`
  let g (n y : ℤ) : ℤ := max 0 (min n ((y - x) / 2))
  -- the counts over the blocks `A, A - 2, …` and `A, A + 2, …` of length `n`
  have h_falling (A : ℤ) (n : ℕ) : ∑ b : Fin n, φ (A - 2 * b) = g n (A + 1) :=
    sum_ite_lt_sub_two_mul x A n
  have h_rising (A : ℤ) (n : ℕ) : ∑ b : Fin n, φ (A + 2 * b) = g n (A + 2 * n - 1) :=
    sum_ite_lt_add_two_mul x A n
  have h_sizes : D.k + D.t + 1 ≤ D.halfGap := D.k_add_t_add_one_le_halfGap
  have h_gap : D.gap = 2 * D.halfGap := rfl
  -- the counts on `Y^m_m` and on `Ỹ^m_m`, for a base of `Y` with `r` entries
  let countY (r m : ℕ) : ℤ := ∑ n ∈ range r, φ (2 * D.targetParameter τ n) +
    ∑ l ∈ range m, g D.t (2 * D.liftWeight (l + 1) τ + D.t) + ∑ l ∈ range m,
      g D.t (-2 * D.liftWeight (l + 1) τ + D.t)
  let countYTilde (r m : ℕ) : ℤ := ∑ n ∈ range (r + 1), φ (-(2 * D.targetParameter τ n) - 1) +
    ∑ l ∈ range m, g (D.t + 1) (-2 * D.liftWeight (l + 1) τ + D.t + 1) +
    ∑ l ∈ range m, g (D.t - 1) (2 * D.liftWeight (l + 1) τ + D.t - 1)
  have h_bound (m : ℕ) : countYTilde (D.k - 1 + m) m - countY (D.k - 1 + m) m ∈
      Icc (φ (2 * D.targetParameter τ (D.k - 1 + m)))
        (φ (-(2 * D.targetParameter τ (D.k - 1 + m)) - 1)) := by
    induction m with
    | zero => simpa [countY, countYTilde, φ] using D.sum_ite_targetParameter_sub_sum_ite_mem_Icc τ x
    | succ m ih =>
      -- The down blocks at `-w_(m+1)` lie between the entries `k - 1 + m` and `k + m` of the target
      -- parameter, and the up blocks at `w_(m+1)` between their negatives.
      have h_succ : D.liftWeight (m + 1 + 1) τ = D.liftWeight (m + 1) τ + D.gap := by grind
      have h_down :
          g (D.t + 1) (-2 * D.liftWeight (m + 1) τ + D.t + 1) - g D.t
            (-2 * D.liftWeight (m + 1) τ + D.t) ∈
            Icc (φ (2 * D.targetParameter τ (D.k - 1 + (m + 1))))
              (φ (2 * D.targetParameter τ (D.k - 1 + m))) := by
        rw [targetParameter_sub_one_add, targetParameter_sub_one_add]
        exact max_min_succ_sub_max_min_mem_Icc x (by omega) (by omega) (by omega)
      have h_up : g D.t (2 * D.liftWeight (m + 1) τ + D.t) - g (D.t - 1)
        (2 * D.liftWeight (m + 1) τ + D.t - 1) ∈
          Icc (φ (-(2 * D.targetParameter τ (D.k - 1 + m)) - 1))
            (φ (-(2 * D.targetParameter τ (D.k - 1 + (m + 1))) - 1)) := by
        rw [targetParameter_sub_one_add, targetParameter_sub_one_add]
        simpa only [sub_add_cancel, ← add_sub_assoc] using
          max_min_succ_sub_max_min_mem_Icc x (n := D.t - 1) (c := 2 * D.liftWeight (m + 1) τ)
            (by grind [D.t_odd.pos]) (by omega) (by omega)
      simp only [countY, countYTilde, ← add_assoc, sum_range_succ, mem_Icc] at ih h_down h_up ⊢
      omega
  have h_false : ∑ y, φ (D.gridParam false 0 D.m D.m τ y) = countY D.r D.m := by
    rw [← D.gridBlockEquiv.symm.sum_comp]
    simp [countY, gridParam_false, ← two_mul D.m, sum_prod_type, sum_range, h_falling]
  have h_true : ∑ y', φ ((-D.gridParam true 0 D.m D.m τ) y') = countYTilde D.r D.m := by
    rw [← D.gridBlockEquiv.symm.sum_comp]
    simp only [countYTilde, neg_gridParam_true, Equiv.apply_symm_apply, sum_sum_type, sum_prod_type,
      Sum.elim_inl, Sum.elim_inr, h_rising, sum_range, Bool.toNat_true,
      Nat.cast_pred D.t_odd.pos, Nat.cast_succ]
    ring_nf
  push_cast [card_filter]
  change ∑ y', φ ((-D.gridParam true 0 D.m D.m τ) y') -
    ∑ y, φ (D.gridParam false 0 D.m D.m τ y) ∈ Icc 0 1
  rw [h_true, h_false, h_rank]
  exact Icc_subset_Icc (ite_nonneg zero_le_one le_rfl) (ite_le_one le_rfl zero_le_one) (h_bound D.m)

/-- For `i, j ≤ m` and offset `0`, all entries of the doubled parameter at the node `(i, j)` have
absolute value at most `⌈20 b⌉`, where `b = D.b = exp D.logB`. -/
lemma abs_gridParam_le (hi : i ≤ D.m) (hj : j ≤ D.m) (x : D.GridIndex z i j) :
    |D.gridParam z 0 i j τ x| ≤ ⌈20 * D.b⌉₊ := by
  -- each entry is bounded by `10 * w (2 * m)`
  have h_top : 10 * D.liftWeight (2 * D.m) τ ≤ ⌈20 * D.b⌉₊ := by
    rify
    linarith [D.liftWeight_le_two_mul_b (le_refl (2 * D.m)) τ, Nat.le_ceil (20 * D.b)]
  grw [← h_top, gridParam]
  rcases D.gridBlockEquiv x with (n | ⟨l, b⟩) | ⟨l, b⟩ <;> grind [targetParameter_eq]

/-- For `i, j ≤ m`, the node `(i, j)` of either grid has rank at most `2 * D.n m`, where
`D.n m = k + m (t + 1)`. -/
lemma card_gridIndex_le (hi : i ≤ D.m) (hj : j ≤ D.m) :
    Fintype.card (D.GridIndex z i j) ≤ 2 * D.n D.m :=
  calc
    _ = D.r + z.toNat + i * (D.t + z.toNat) + j * (D.t - z.toNat) := D.card_gridIndex
    _ ≤ D.r + z.toNat + D.m * (D.t + z.toNat) + D.m * (D.t - z.toNat) := by gcongr
    _ ≤ 2 * (D.k + D.m * (D.t + 1)) := by grind [mul_tsub, Bool]

instance : Nonempty (D.GridIndex z i j) := by
  rw [← card_pos_iff, D.card_gridIndex]
  grind

/-! ### The centres of a grid and the blocks of its nodes -/

/-- The entries of the target parameter at `τ` are strictly decreasing. -/
lemma targetParameter_strictAnti : StrictAnti (D.targetParameter τ) := by
  grind [strictAnti_nat_of_succ_lt, targetParameter_eq]

/-- The entries of the target parameter are at most `k / 2`. -/
lemma two_mul_targetParameter_le (n : ℕ) : 2 * D.targetParameter τ n ≤ D.k := by
  grind [targetParameter_eq]

lemma gap_le_liftWeight_succ (l : ℕ) : D.gap ≤ D.liftWeight (l + 1) τ := D.nat_le_of_hasLogBound

/-- For `l < l'`, the weight `D.liftWeight (l' + 1) τ` exceeds `D.liftWeight (l + 1) τ` by at least
the gap `D.gap`. -/
lemma liftWeight_succ_add_gap_le {l l' : ℕ} (h_lt : l < l') :
    D.liftWeight (l + 1) τ + D.gap ≤ D.liftWeight (l' + 1) τ := by
  have h_mul : (l + 1 + 1) * D.gap ≤ (l' + 1) * D.gap := Nat.mul_le_mul_right D.gap (by omega)
  grind

/-- For `p < D.posRank j = D.k + j - 1`, the entry `p` of the target parameter at the infinite place
`τ` lies at least `D.halfGap` above the centre `-D.liftWeight j τ`: `D.halfGap ≤ D.targetParameter τ
p + D.liftWeight j τ`. -/
lemma halfGap_le_targetParameter_add_liftWeight {p : ℕ} (hp : p < D.posRank j) :
    D.halfGap ≤ D.targetParameter τ p + D.liftWeight j τ := by
  rw [posRank] at hp
  rw [targetParameter_eq]
  split_ifs with h_first
  · -- The entry is at least `-k`, small against `w_j ≥ D.gap = 2 halfGap`.
    have h_large : D.gap ≤ D.liftWeight j τ := D.nat_le_of_hasLogBound
    have h_sizes : D.k + D.t + 1 ≤ D.halfGap := D.k_add_t_add_one_le_halfGap
    have h_gap : D.gap = 2 * D.halfGap := rfl
    omega
  · -- The entry is `halfGap - w_a` with `a = p + 2 - k ≤ j`.
    have h_index : p + 2 - D.k ≤ j := by omega
    rcases h_index.eq_or_lt with h_eq | h_lt
    · rw [h_eq, sub_add_cancel]
    · have h_below : D.liftWeight (p + 2 - D.k) τ + (if p + 2 - D.k + 1 < j then 2 else 1) * D.gap ≤
          D.liftWeight j τ := D.liftWeight_add_gap_le τ (p + 2 - D.k) j h_lt
      split_ifs at h_below <;> omega

/-- For `D.posRank j = D.k + j - 1 ≤ p`, the entry `p` of the target parameter lies at least
`D.halfGap` below the centre `-D.liftWeight j τ`. -/
lemma targetParameter_add_liftWeight_le_neg_halfGap {p : ℕ} (hp : D.posRank j ≤ p) :
    D.targetParameter τ p + D.liftWeight j τ ≤ -D.halfGap := by
  -- The entry is `halfGap - w_a` with `a = p + 2 - k > j`, and `w_a ≥ w_j + D.gap` with
  -- `D.gap = 2 halfGap`.
  rw [posRank] at hp
  have h_k : 0 < D.k := D.k_pos
  have h_gap : D.gap = 2 * D.halfGap := rfl
  have h_above : D.liftWeight j τ + (if j + 1 < p + 2 - D.k then 2 else 1) * D.gap ≤ D.liftWeight
    (p + 2 - D.k) τ :=
    D.liftWeight_add_gap_le τ j (p + 2 - D.k) (by omega)
  rw [targetParameter_eq, ite_eq_right (by omega)]
  split_ifs at h_above <;> omega

/-- The centre `-D.liftWeight j τ` is at distance at least `D.halfGap` from the entries of
`D.targetParameter τ`. The entry `p` lies above it if `p < D.posRank j = k + j - 1`, and below it
otherwise. The two cases are `halfGap_le_targetParameter_add_liftWeight` and
`targetParameter_add_liftWeight_le_neg_halfGap`. -/
lemma targetParameter_add_liftWeight_gap (j : ℕ) (τ : D.Φ) (p : ℕ) :
    if p < D.posRank j then D.halfGap ≤ D.targetParameter τ p + D.liftWeight j τ
    else D.targetParameter τ p + D.liftWeight j τ ≤ -D.halfGap := by
  split_ifs with hp
  · exact D.halfGap_le_targetParameter_add_liftWeight τ hp
  · exact D.targetParameter_add_liftWeight_le_neg_halfGap τ (not_lt.1 hp)

/-- The centres of the grid `z` at `τ`: for `l < m` an up centre `w_(l+1)`, named `inl l`, and a
down centre `-w_(l+1)`, named `inr l`. The lengths are `t` in grid `Y`, and `t + 1` and `t - 1` in
grid `Ỹ`. The stem is the parameter on the base. In grid `Ỹ` this is the negative of the system of
the spaces `Ỹ^i_j`, whose up and down centres are exchanged. -/
def gridCentres (z : Bool) : CentreSystem (ℕ ⊕ ℕ) where
  centres := (range D.m).disjSum (range D.m)
  centre := Sum.elim (fun l : ℕ ↦ D.liftWeight (l + 1) τ) fun l : ℕ ↦ -D.liftWeight (l + 1) τ
  length := Sum.elim (fun _ : ℕ ↦ D.t + z.toNat) fun _ : ℕ ↦ D.t - z.toNat
  isUp := Sum.isLeft
  stem := (range (D.r + z.toNat)).image fun n : ℕ ↦ 2 * D.targetParameter τ n + z.toNat

/-- The centres whose blocks are present at the node `(i, j)` with offset `o`: the up centres
`l < i` and the down centres `o ≤ l < o + j`. -/
def gridBlocks (o i j : ℕ) : Finset (ℕ ⊕ ℕ) := (range i).disjSum (Ico o (o + j))

/-- The step from `(i, j)` to `(i + 1, j)` adds the up centre `i`. -/
lemma gridBlocks_succ_left (o i j : ℕ) :
    gridBlocks o (i + 1) j = insert (.inl i) (gridBlocks o i j) := by
  ext (l | l) <;> grind [gridBlocks, inl_mem_disjSum, inr_mem_disjSum]

/-- The step from `(i, j)` to `(i, j + 1)` adds the down centre `j + o`. -/
lemma gridBlocks_succ_right (o i j : ℕ) :
    gridBlocks o i (j + 1) = insert (.inr (j + o)) (gridBlocks o i j) := by
  ext (l | l) <;> grind [gridBlocks, inl_mem_disjSum, inr_mem_disjSum]

/-- The node `(i, j + 1)` with offset `o` has the centres of the node `(i, j)` with offset `o + 1`
and the down centre `o`. -/
lemma gridBlocks_succ_right_eq_insert_first (o i j : ℕ) :
    gridBlocks o i (j + 1) = insert (.inr o) (gridBlocks (o + 1) i j) := by
  ext (l | l) <;> grind [gridBlocks, inl_mem_disjSum, inr_mem_disjSum]

lemma card_stem_gridCentres (z : Bool) : #(D.gridCentres τ z).stem = D.r + z.toNat := by
  have h_inj : Injective fun n : ℕ ↦ 2 * D.targetParameter τ n + z.toNat :=
    fun a b hab ↦ (D.targetParameter_strictAnti τ).injective (by simpa using hab)
  rw [gridCentres, card_image_of_injective _ h_inj, card_range]

/-- For `i ≤ D.m` and `o + j ≤ D.m`, the centres `gridBlocks o i j` of the node `(i, j)` with offset
`o` lie in the centres `(D.gridCentres τ z).centres` of the grid `z` at `τ`. -/
lemma gridBlocks_subset (z : Bool) (hi : i ≤ D.m) (hj : o + j ≤ D.m) :
    gridBlocks o i j ⊆ (D.gridCentres τ z).centres :=
  disjSum_mono (range_subset_range.2 hi) (by grind)

end Nodes

/-- At an infinite place `τ` of the field `D.E`, the centres `±w_(l+1)(τ)`, `l < m`, of the grid `z`
are separated by `Δ - t - 2`. The block lengths have the parity of the size of the stem, the
parameter on the base. For each centre `c`, the doubled entries of the stem and of the blocks of the
other centres are at distance at least `Δ - t - 2` plus the block length of `c` from `2c`. -/
lemma isSeparated_gridCentres {P : Parameters} (D : Data P) (τ : D.Φ) (z : Bool) :
    (D.gridCentres τ z).IsSeparated (D.gap - D.t - 2) := by
  have h_z : z.toNat ≤ 1 := z.toNat_le
  have h_sizes : D.k + D.t + 1 ≤ D.halfGap := D.k_add_t_add_one_le_halfGap
  have h_gap : D.gap = 2 * D.halfGap := rfl
  refine ⟨?length_mod_two, ?odd_add_card, ?stem_far, ?block_far⟩
  case length_mod_two =>
    rw [card_stem_gridCentres]
    simp only [gridCentres]
    rintro (l | l) - <;> grind [D.t_odd, D.r_odd]
  case odd_add_card =>
    rw [card_stem_gridCentres, gridCentres]
    grind [D.r_odd]
  case stem_far =>
    rintro c - y hy
    obtain ⟨n, -, rfl⟩ := mem_image.1 hy
    rcases c with l | l
    · have h_stem : 2 * D.targetParameter τ n ≤ D.k := D.two_mul_targetParameter_le τ n
      have h_centre : D.gap ≤ D.liftWeight (l + 1) τ := D.gap_le_liftWeight_succ τ l
      simp only [gridCentres, Sum.elim_inl, le_abs]
      omega
    · have h_far : D.halfGap ≤ D.targetParameter τ n + D.liftWeight (l + 1) τ ∨
          D.targetParameter τ n + D.liftWeight (l + 1) τ ≤ -D.halfGap :=
        (lt_or_ge n (D.posRank (l + 1))).imp (D.halfGap_le_targetParameter_add_liftWeight τ)
          (D.targetParameter_add_liftWeight_le_neg_halfGap τ)
      simp only [gridCentres, Sum.elim_inr, le_abs]
      omega
  case block_far =>
    -- in all four cases the two centres are at least `D.gap` apart
    rintro (l | l) - (l' | l') - hne y hy
    all_goals
      obtain ⟨b, hb, rfl⟩ := mem_centredBlock.1 hy
      have h_centre : D.gap ≤ D.liftWeight (l + 1) τ := D.gap_le_liftWeight_succ τ l
      have h_centre' : D.gap ≤ D.liftWeight (l' + 1) τ := D.gap_le_liftWeight_succ τ l'
      have h_lt : l < l' → D.liftWeight (l + 1) τ + D.gap ≤ D.liftWeight (l' + 1) τ :=
        D.liftWeight_succ_add_gap_le τ
      have h_gt : l' < l → D.liftWeight (l' + 1) τ + D.gap ≤ D.liftWeight (l + 1) τ :=
        D.liftWeight_succ_add_gap_le τ
      simp only [gridCentres, Sum.elim_inl, Sum.elim_inr, le_abs, ne_eq, Sum.inl.injEq,
        Sum.inr.injEq] at hb hne ⊢
      omega

section Entries

variable {j : ℕ} {P : Parameters} (D : Data P) {z : Bool} {o i : ℕ} (τ : D.Φ)

/-- The sign `entrySign o j a` is `-1` if `o + a + min (a - o) j` is odd and `1` otherwise. Let
`a ≤ D.m`. Let `y` be a doubled entry with `y ≤ 2 * D.liftWeight (l + 1) τ` for all `l ≥ i`. For `l`
outside `[o, o + j)`, let `y < -2 * D.liftWeight (l + 1) τ` hold exactly if `l < a`. Then
`entrySign o j a` is `(-1) ^ o` times the sign of `y` in `D.gridCentres τ z`, the centres of grid
`z` at the place `τ` (`CentreSystem.sign`). -/
lemma entrySign_eq_mul_sign {a : ℕ} {y : ℤ} (ha : a ≤ D.m)
    (h_up : ∀ l : ℕ, i ≤ l → y ≤ 2 * D.liftWeight (l + 1) τ)
    (h_down : ∀ l : ℕ, l ∉ Ico o (o + j) → (y < 2 * -(D.liftWeight (l + 1) τ : ℤ) ↔ l < a)) :
    entrySign o j a = (-1) ^ o * (D.gridCentres τ z).sign (gridBlocks o i j) y := by
  have h_set : {c ∈ (D.gridCentres τ z).centres \ gridBlocks o i j |
      (D.gridCentres τ z).CountsFor c y} = (range a \ Ico o (o + j)).map .inr := by
    ext c
    rw [mem_filter, mem_sdiff]
    rcases c with l | l
    · simpa [gridCentres, gridBlocks, CentreSystem.CountsFor] using fun _ ↦ h_up l
    · suffices (l < D.m ∧ l ∉ Ico o (o + j)) ∧ y < 2 * -(D.liftWeight (l + 1) τ : ℤ) ↔
          l < a ∧ l ∉ Ico o (o + j) by
        simpa [gridCentres, gridBlocks, CentreSystem.CountsFor, -mem_Ico]
      grind
  have h_count : #(range a \ Ico o (o + j)) + min (a - o) j = a := by
    rw [card_sdiff, range_eq_Ico, Ico_inter_Ico, Nat.card_Ico, Nat.card_Ico]
    omega
  rw [CentreSystem.sign, h_set, card_map, entrySign_eq_neg_one_pow, ← pow_add]
  exact neg_one_pow_congr (by grind)

/-- The doubled entries at the node `(i, j)` of grid `z` with offset `o` and the infinite place `τ`,
after the lowering is undone; the lowering is `1` in grid `Y` for odd `i + j`, else `0`. Read `z` as
`0` or `1`, and put `λ_n = D.targetParameter τ n` and `w_a = D.liftWeight a τ`. The base entry with
number `n` is `2 λ_n + z`. The entry at the position `b` of the block `l` is
`2 w_(l+1) + (t + z) - 1 - 2 b` for a block of the first kind (`l < i`) and
`-2 w_(o+l+1) + (t - z) - 1 - 2 b` for a block of the second kind (`l < j`). -/
lemma gridParam_add_lowering (τ : D.Φ) (x : D.GridIndex z i j) :
    D.gridParam z o i j τ x + (D.gridCentres τ z).lowering (gridBlocks o i j) =
      (D.gridBlockEquiv x).elim
        (Sum.elim (fun n : Fin (D.r + z.toNat) ↦ 2 * D.targetParameter τ n.val + z.toNat)
          fun (l, b) ↦ (2 * D.liftWeight (l + 1) τ + (D.t + z.toNat : ℕ) - 1 - 2 * b : ℤ))
        fun (l, b) ↦ (2 * -D.liftWeight (o + l + 1) τ + (D.t - z.toNat : ℕ) - 1 - 2 * b : ℤ) := by
  have h_lowering : (D.gridCentres τ z).lowering (gridBlocks o i j) =
      if z = false ∧ (j + i) % 2 = 1 then 1 else 0 := by
    simp only [CentreSystem.lowering, card_stem_gridCentres, gridBlocks, card_disjSum, card_range,
      Nat.card_Ico]
    grind
  rw [h_lowering, gridParam]
  rcases D.gridBlockEquiv x with (n | ⟨l, b⟩) | ⟨l, b⟩ <;> grind

/-- Take two entries of the target parameter with numbers `n` and `n'`, where
`n + 1 - D.k ≠ n' + 1 - D.k` (truncated subtraction). They differ by at least the gap `D.gap`. -/
lemma gap_le_abs_targetParameter_sub {n n' : ℕ} (hne : n + 1 - D.k ≠ n' + 1 - D.k) :
    D.gap ≤ |D.targetParameter τ n - D.targetParameter τ n'| := by
  wlog h_lt : n + 1 - D.k < n' + 1 - D.k generalizing n n' with h_main
  · rw [abs_sub_comm]
    exact h_main hne.symm (by omega)
  -- The later entry is `halfGap - w_(a+1)` with `a = n' + 1 - k` positive.
  have h_step : D.liftWeight (n + 1 - D.k + 1) τ + D.gap ≤ D.liftWeight (n' + 1 - D.k + 1) τ :=
    D.liftWeight_succ_add_gap_le τ h_lt
  have h_centre : D.gap ≤ D.liftWeight (n + 1 - D.k + 1) τ :=
    D.gap_le_liftWeight_succ τ (n + 1 - D.k)
  have h_sizes : D.k + D.t + 1 ≤ D.halfGap := D.k_add_t_add_one_le_halfGap
  grind [targetParameter_eq]

/-- For `l < j`, if the base entry with number `n` at the node `(i, j)` with offset `o` has sign
`entrySign o j (n + 1 - D.k) ≠ 1`, then `D.targetParameter τ n` is at distance at least
`3 * D.halfGap` from the block centre `-D.liftWeight (o + l + 1) τ`. The reason is that the two
entries of the target parameter next to this centre have the sign `+1`. -/
lemma three_mul_halfGap_le_abs_targetParameter_add_liftWeight {n l : ℕ} (hl : l < j)
    (h_sign : entrySign o j (n + 1 - D.k) ≠ 1) :
    3 * D.halfGap ≤ |D.targetParameter τ n + D.liftWeight (o + l + 1) τ| := by
  have h_sizes : D.k + D.t + 1 ≤ D.halfGap := D.k_add_t_add_one_le_halfGap
  have h_gap : D.gap = 2 * D.halfGap := rfl
  have h_ne : n + 1 - D.k ≠ o + l ∧ n + 1 - D.k ≠ o + l + 1 := by grind [entrySign_eq_ite]
  have h_above : n + 2 - D.k < o + l + 1 →
      D.liftWeight (n + 2 - D.k) τ + D.gap ≤ D.liftWeight (o + l + 1) τ := by
    intro h_lt
    have h_le := D.liftWeight_add_gap_le τ _ _ h_lt
    split_ifs at h_le <;> omega
  have h_below : o + l + 2 < n + 2 - D.k →
      D.liftWeight (o + l + 1) τ + 2 * D.gap ≤ D.liftWeight (n + 2 - D.k) τ := by
    intro h_lt
    have h_le := D.liftWeight_add_gap_le τ (o + l + 1) (n + 2 - D.k) (by omega)
    rwa [ite_eq_left h_lt] at h_le
  have h_far : 2 * D.gap ≤ D.liftWeight (o + l + 1) τ := D.nat_le_of_hasLogBound
  rw [targetParameter_eq, le_abs]
  split_ifs <;> omega

end Entries

/-- At an infinite place `τ` the doubled parameter of the node `(i, j)` of grid `z` with offset `o`
takes distinct values at distinct indices. -/
lemma gridParam_injective {j : ℕ} {P : Parameters} (D : Data P) {z : Bool} {o i : ℕ} (τ : D.Φ) :
    Injective (D.gridParam z o i j τ) := by
  intro x y hxy
  have h_eq : D.gridParam z o i j τ x + (D.gridCentres τ z).lowering (gridBlocks o i j) =
      D.gridParam z o i j τ y + (D.gridCentres τ z).lowering (gridBlocks o i j) := by rw [hxy]
  rw [gridParam_add_lowering, gridParam_add_lowering] at h_eq
  -- The base entries are distinct. The blocks are short against the distance of their centres
  -- from each other and from the base entries.
  have h_z : z.toNat ≤ 1 := z.toNat_le
  have h_sizes : D.k + D.t + 1 ≤ D.halfGap := D.k_add_t_add_one_le_halfGap
  have h_gap : D.gap = 2 * D.halfGap := rfl
  have h_base (n n' : ℕ) (h_row : D.targetParameter τ n = D.targetParameter τ n') : n = n' :=
    (D.targetParameter_strictAnti τ).injective h_row
  have h_stem (n : ℕ) : 2 * D.targetParameter τ n ≤ D.k := D.two_mul_targetParameter_le τ n
  have h_centre (l : ℕ) : D.gap ≤ D.liftWeight (l + 1) τ := D.gap_le_liftWeight_succ τ l
  have h_apart (l l' : ℕ) (h_near : |(D.liftWeight (l + 1) τ - D.liftWeight (l' + 1) τ : ℤ)| <
    D.gap) : l = l' := by
    have h_lt : l < l' → D.liftWeight (l + 1) τ + D.gap ≤ D.liftWeight (l' + 1) τ :=
      D.liftWeight_succ_add_gap_le τ
    have h_gt : l' < l → D.liftWeight (l' + 1) τ + D.gap ≤ D.liftWeight (l + 1) τ :=
      D.liftWeight_succ_add_gap_le τ
    rw [abs_lt] at h_near
    omega
  have h_far (n l : ℕ) :
      D.halfGap ≤ D.targetParameter τ n + D.liftWeight l τ ∨ D.targetParameter τ n + D.liftWeight l
        τ ≤
        -D.halfGap :=
    (lt_or_ge n (D.posRank l)).imp (D.halfGap_le_targetParameter_add_liftWeight τ)
      (D.targetParameter_add_liftWeight_le_neg_halfGap τ)
  refine D.gridBlockEquiv.injective ?_
  revert h_eq
  -- Each index lies in the base, in an up block or in a down block.
  rcases D.gridBlockEquiv x with (⟨n, hn⟩ | ⟨⟨l, hl⟩, b, hb⟩) | ⟨⟨l, hl⟩, b, hb⟩ <;>
    rcases D.gridBlockEquiv y with (⟨n', hn'⟩ | ⟨⟨l', hl'⟩, b', hb'⟩) | ⟨⟨l', hl'⟩, b', hb'⟩ <;>
    simp only [Sum.elim_inl, Sum.elim_inr, Sum.inl.injEq, Fin.mk.injEq, reduceCtorEq]
  · grind only [h_base n n']
  · grind only [h_stem n, h_centre l']
  · grind only [h_far n (o + l' + 1)]
  · grind only [h_stem n', h_centre l]
  · grind [h_apart l l']
  · grind only [h_centre l, h_centre (o + l')]
  · grind only [h_far n' (o + l + 1)]
  · grind only [h_centre l', h_centre (o + l)]
  · grind [h_apart (o + l) (o + l')]

section Steps

variable {j : ℕ} {P : Parameters} (D : Data P) {z : Bool} {o i : ℕ} (τ : D.Φ)

/-- Each entry of the doubled parameter `D.gridParam z o i j τ` at the node `(i, j)` has the parity
of `card (D.GridIndex z i j) - 1`, the size of the index set minus one. -/
lemma even_gridParam_add_card_sub_one (x : D.GridIndex z i j) :
    Even (D.gridParam z o i j τ x + card (D.GridIndex z i j) - 1) := by
  have h_t : D.t % 2 = 1 := Nat.odd_iff.1 D.t_odd
  have h_rank : card (D.GridIndex z i j) % 2 = (if z then 0 else (i + j + 1) % 2) :=
    D.card_gridIndex_mod_two z i j
  generalize card (D.GridIndex z i j) = N at h_rank ⊢
  rw [Int.even_iff, gridParam]
  rcases D.gridBlockEquiv x with (n | ⟨l, b⟩) | ⟨l, b⟩ <;> grind

/-- At the infinite place `τ`, two entries of the doubled parameter at a node whose signs differ
are at least `2 * D.gap = 4 * D.halfGap` apart. -/
lemma two_mul_gap_le_abs_gridParam_sub {x y : D.GridIndex z i j}
    (h_sign : D.gridSigns z o i j x ≠ D.gridSigns z o i j y) :
    2 * D.gap ≤ |D.gridParam z o i j τ x - D.gridParam z o i j τ y| := by
  have h_z : z.toNat ≤ 1 := z.toNat_le
  have h_sizes : D.k + D.t + 1 ≤ D.halfGap := D.k_add_t_add_one_le_halfGap
  have h_gap : D.gap = 2 * D.halfGap := rfl
  wlog h_neg : D.gridSigns z o i j x ≠ 1 generalizing x y with h_main
  · rw [abs_sub_comm]
    exact h_main h_sign.symm (by grind)
  -- The added blocks have the sign `+1`, so `x`, of sign `-1`, is a base index.
  obtain ⟨n, hx⟩ : ∃ n : Fin (D.r + z.toNat), D.gridBlockEquiv x = .inl (.inl n) := by
    rcases hx : D.gridBlockEquiv x with (n | p) | p <;> simp_all [gridSigns]
  rw [← add_sub_add_right_eq_sub _ _ ((D.gridCentres τ z).lowering (gridBlocks o i j)),
    gridParam_add_lowering, gridParam_add_lowering]
  rcases hy : D.gridBlockEquiv y with (n' | ⟨⟨l, hl⟩, b, hb⟩) | ⟨⟨l, hl⟩, b, hb⟩ <;>
    simp only [gridSigns, hx, hy, Sum.elim_inl, Sum.elim_inr, le_abs] at h_sign h_neg ⊢
  · -- `y` lies in the base
    have h_far : D.gap ≤ |D.targetParameter τ n - D.targetParameter τ n'| :=
      D.gap_le_abs_targetParameter_sub τ fun h_eq ↦ h_sign (by rw [h_eq])
    grind
  · -- `y` lies in an up block
    have h_stem : 2 * D.targetParameter τ n ≤ D.k := D.two_mul_targetParameter_le τ n
    have h_centre : 2 * D.gap ≤ D.liftWeight (l + 1) τ := D.nat_le_of_hasLogBound
    omega
  · -- `y` lies in a down block
    have h_far : 3 * D.halfGap ≤ |D.targetParameter τ n + D.liftWeight (o + l + 1) τ| :=
      D.three_mul_halfGap_le_abs_targetParameter_add_liftWeight τ hl h_neg
    grind

/-- The doubled parameter `D.gridParam z o i j τ` at the node `(i, j)` with offset `o` has, at the
infinite place `τ`, the gap `D.gap` for the signs of the node (`HasGap`): its entries are distinct,
have the parity of the rank minus one, and differ by at least `2 * D.gap` where the signs differ. -/
lemma hasGap_gridParam (z : Bool) (o i j : ℕ) : (D.gridParam z o i j τ).HasGap D.gap where
  injective := D.gridParam_injective τ
  parity := D.even_gridParam_add_card_sub_one τ
  gap _ _ := D.two_mul_gap_le_abs_gridParam_sub τ

/-- Let `o + j ≤ m`, with `o = 0` (the grids) or `i = 0` (the triangles). For every infinite place
`τ`, the sign at the index `x` of the node `(i, j)` with offset `o` is `(-1) ^ o * (-1) ^ N`. Let
`y` be the doubled entry `gridParam` at `τ` and `x`, plus `1` if the stem of `D.gridCentres τ z` and
the set `gridBlocks o i j` both have odd size. Then `N` is the number of centres outside
`gridBlocks o i j` that are up and below `y / 2`, or down and above `y / 2`. -/
lemma gridSigns_eq_mul_sign (hj : o + j ≤ D.m) (h_zero : o = 0 ∨ i = 0) (x : D.GridIndex z i j) :
    D.gridSigns z o i j x = (-1) ^ o * (D.gridCentres τ z).sign (gridBlocks o i j)
      (D.gridParam z o i j τ x + (D.gridCentres τ z).lowering (gridBlocks o i j)) := by
  have h_z : z.toNat ≤ 1 := z.toNat_le
  have h_sizes : D.k + D.t + 1 ≤ D.halfGap := D.k_add_t_add_one_le_halfGap
  have h_gap : D.gap = 2 * D.halfGap := rfl
  rw [gridParam_add_lowering, gridSigns]
  rcases D.gridBlockEquiv x with (⟨n, hn⟩ | ⟨⟨l, hl⟩, b, hb⟩) | ⟨⟨l, hl⟩, b, hb⟩
  all_goals simp only [Sum.elim_inl, Sum.elim_inr, Pi.one_apply]
  · -- A base entry with number `n` lies below the down centres `l' < n + 1 - k`.
    have h_rank : D.r + 1 = D.k + D.m := D.r_add_one
    refine D.entrySign_eq_mul_sign τ (by omega) (fun l' _ ↦ ?_) fun l' _ ↦ ?_
    · have h_stem : 2 * D.targetParameter τ n ≤ D.k := D.two_mul_targetParameter_le τ n
      have h_centre : D.gap ≤ D.liftWeight (l' + 1) τ := D.gap_le_liftWeight_succ τ l'
      omega
    · have h_above : n < D.k + (l' + 1) - 1 → D.halfGap ≤ D.targetParameter τ n + D.liftWeight
        (l' + 1)
        τ :=
        D.halfGap_le_targetParameter_add_liftWeight τ
      have h_below : D.k + (l' + 1) - 1 ≤ n → D.targetParameter τ n + D.liftWeight (l' + 1) τ ≤
        -D.halfGap :=
        D.targetParameter_add_liftWeight_le_neg_halfGap τ
      omega
  · -- An up block lies above all down centres, and it occurs only for `o = 0`.
    obtain rfl : o = 0 := by omega
    have h_sign : entrySign 0 j 0 = 1 := by simp [entrySign_eq_neg_one_pow]
    refine h_sign.symm.trans
      (D.entrySign_eq_mul_sign τ D.m.zero_le (fun l' hl' ↦ ?_) fun l' _ ↦ ?_)
    · have h_far : D.liftWeight (l + 1) τ + D.gap ≤ D.liftWeight (l' + 1) τ :=
        D.liftWeight_succ_add_gap_le τ (by omega)
      omega
    · have h_centre : D.gap ≤ D.liftWeight (l + 1) τ := D.gap_le_liftWeight_succ τ l
      omega
  · -- The missing down centres above a down block are those with `l' < o`.
    have h_sign : entrySign o j o = 1 := by simp [entrySign_eq_neg_one_pow, ← two_mul]
    refine h_sign.symm.trans
      (D.entrySign_eq_mul_sign τ (by omega) (fun l' _ ↦ ?_) fun l' hl' ↦ ?_)
    · have h_centre : D.gap ≤ D.liftWeight (l' + 1) τ := D.gap_le_liftWeight_succ τ l'
      omega
    · have h_lt : l' < o + l → D.liftWeight (l' + 1) τ + D.gap ≤ D.liftWeight (o + l + 1) τ :=
        D.liftWeight_succ_add_gap_le τ
      have h_gt : o + l < l' → D.liftWeight (o + l + 1) τ + D.gap ≤ D.liftWeight (l' + 1) τ :=
        D.liftWeight_succ_add_gap_le τ
      rw [mem_Ico] at hl'
      omega

/-- Let `τ` be an infinite place of the field `D.E`, let `o + j ≤ m`, and let `o = 0` or `i = 0`.
The doubled parameter at `τ` of the node `(i, j)` of grid `z` with offset `o` is the parameter of
the set `gridBlocks o i j` in the system `D.gridCentres τ z`. -/
lemma isParam_gridParam (τ : D.Φ) (z : Bool) (hj : o + j ≤ D.m) (h_zero : o = 0 ∨ i = 0) :
    (D.gridCentres τ z).IsParam (gridBlocks o i j) ((-1) ^ o) (D.gridParam z o i j τ) := by
  refine ⟨?_, ?_, D.gridSigns_eq_mul_sign τ hj h_zero⟩
  · rw [card_gridIndex, CentreSystem.rank, card_stem_gridCentres]
    simp [gridBlocks, gridCentres, add_assoc]
  · have h_shift (p : ℕ → Prop) :
        (∃ l : ℕ, (o ≤ l ∧ l < o + j) ∧ p l) ↔ ∃ l < j, p (o + l) :=
      ⟨fun ⟨l, hl, hp⟩ ↦ ⟨l - o, by grind⟩, fun ⟨l, h_lt, hp⟩ ↦ ⟨o + l, by omega, hp⟩⟩
    ext y
    simp only [gridParam_add_lowering, mem_image, mem_univ, true_and]
    rw [D.gridBlockEquiv.exists_congr_left]
    simp [CentreSystem.entries, CentreSystem.block, gridCentres, gridBlocks, mem_centredBlock,
      Fin.exists_iff, h_shift, or_assoc, eq_comm (a := y)]

/-! ### The parameters at the two ends of a step correspond -/

/-- The separation `D.gap - D.t - 2` of the centres is at least `500 (N + N') ^ 3` for the ranks
`N`, `N'` of two nodes `(i, j)`, `(i', j')` of a grid with `i, j, i', j' ≤ m`. -/
lemma mul_card_gridIndex_add_pow_three_le {i' j' : ℕ} (hi : i ≤ D.m) (hj : j ≤ D.m) (hi' : i' ≤ D.m)
    (hj' : j' ≤ D.m) :
    500 * (card (D.GridIndex z i j) + card (D.GridIndex z i' j')) ^ 3 ≤ D.gap - D.t - 2 := by
  have h_size : 500 * (2 * D.n D.m + 2 * D.n D.m) ^ 3 + D.t + 2 ≤ D.gap := D.nat_le_of_hasLogBound
  grw [D.card_gridIndex_le hi hj, D.card_gridIndex_le hi' hj']
  omega

/-- For `i + 1 ≤ D.m`, `j ≤ D.m` and offset `0`, the negated parameters of the nodes `(i, j)` and
`(i + 1, j)` correspond (`ParamsCorrespond`). The weight of a node with `N` indices is
`D.gridWeight z i`. The step inserts the block of the up centre `D.liftWeight (i + 1) τ`. -/
lemma paramsCorrespond_grid_succ_left (z : Bool) (i j : ℕ) (hi : i + 1 ≤ D.m) (hj : j ≤ D.m) :
    ParamsCorrespond (D.gridWeight z i (D.GridIndex z i j))
      (D.gridWeight z i (D.GridIndex z (i + 1) j))
      (-D.gridParam z 0 i j) (-D.gridParam z 0 (i + 1) j)
      (D.gridSigns z 0 i j) (D.gridSigns z 0 (i + 1) j) := by
  intro τ
  -- In grid `Ỹ` (`z = true`) the ranks are even, so the two roundings of half the rank agree.
  have h_weight (a : ℕ) : D.gridWeight z i (D.GridIndex z a j) τ =
      -(D.gridCentres τ z).centre (.inl i) + ((card (D.GridIndex z a j) : ℤ) + 1) / 2 := by
    simp only [gridWeight, gridCentres, Sum.elim_inl]
    grind [D.card_gridIndex_mod_two z a j]
  have h_param (a : ℕ) :
      (D.gridCentres τ z).IsParam (gridBlocks 0 a j) ((-1) ^ 0) (D.gridParam z 0 a j τ) :=
    D.isParam_gridParam τ z (by omega) (.inl rfl)
  rw [h_weight, h_weight]
  exact (h_param i).isBlockRule_neg_insert_of_up (h_param (i + 1)) (gridBlocks_succ_left 0 i j)
    (D.isSeparated_gridCentres τ z) (D.gridBlocks_subset τ z (by omega) (by omega))
    (inl_mem_disjSum.2 (mem_range.2 hi)) (by simp [gridBlocks])
    (D.mul_card_gridIndex_add_pow_three_le (by omega) hj hi hj) rfl

/-- The weight of the character of a step that inserts the block of the down centre `-w_(l+1)` is
this centre plus half the rank of the node, rounded down. -/
lemma gridWeight_not (z : Bool) (l i j : ℕ) :
    D.gridWeight (!z) l (D.GridIndex z i j) τ =
      (D.gridCentres τ z).centre (.inr l) + (card (D.GridIndex z i j) : ℤ) / 2 := by
  -- In grid `Ỹ` (`z = true`) the ranks are even, so the two roundings of half the rank agree.
  simp only [gridWeight, gridCentres, Sum.elim_inr]
  grind [D.card_gridIndex_mod_two z i j]

/-- The parameters correspond along the edge from `(i, j)` to `(i, j + 1)`, in the grids (`o = 0`)
and in the triangles (`i = 0`). At each infinite place `τ` they satisfy the block rule `IsBlockRule`
for the weights `D.gridWeight (!z) (j + o)` of the two nodes (see `gridWeight_not`). The step
inserts the block of the down centre `-D.liftWeight (j + o + 1) τ`. -/
lemma paramsCorrespond_grid_succ_right (z : Bool) (o i j : ℕ) (hi : i ≤ D.m)
    (hj : j + 1 + o ≤ D.m) (h_zero : o = 0 ∨ i = 0) :
    ParamsCorrespond (D.gridWeight (!z) (j + o) (D.GridIndex z i j))
      (D.gridWeight (!z) (j + o) (D.GridIndex z i (j + 1)))
      (D.gridParam z o i j) (D.gridParam z o i (j + 1))
      (D.gridSigns z o i j) (D.gridSigns z o i (j + 1)) := by
  intro τ
  have h_param (b : ℕ) (hb : b ≤ j + 1) :
      (D.gridCentres τ z).IsParam (gridBlocks o i b) ((-1) ^ o) (D.gridParam z o i b τ) :=
    D.isParam_gridParam τ z (by omega) h_zero
  have h_centre : .inr (j + o) ∈ (D.gridCentres τ z).centres :=
    inr_mem_disjSum.2 (mem_range.2 (by omega))
  rw [gridWeight_not, gridWeight_not]
  exact (h_param j j.le_succ).isBlockRule_insert_of_down (h_param (j + 1) le_rfl)
    (gridBlocks_succ_right o i j) (D.isSeparated_gridCentres τ z)
    (D.gridBlocks_subset τ z hi (by omega)) h_centre (by simp [gridBlocks, add_comm])
    (D.mul_card_gridIndex_add_pow_three_le hi (by omega) hi (by omega)) rfl

/-- Both kinds of step in one statement, for arguments that treat them together: `isLeft = true` is
`paramsCorrespond_grid_succ_left` and `isLeft = false` is `paramsCorrespond_grid_succ_right`. The
equation `h_step` fixes the target `(i', j')` and the weights: at a node of rank `N` the weight
`D.gridWeight weightGrid weightIdx` is `N / 2`, rounded down if `weightGrid` is true and up
otherwise, less `w_(weightIdx+1)`. The target satisfies `i' ≤ m` and `j' + o ≤ m`, and it lies in a
grid (`o = 0`) or in a triangle (`i' = 0`). -/
lemma paramsCorrespond_grid (isLeft z : Bool) (o i j : ℕ) {weightGrid : Bool} {weightIdx i' j' : ℕ}
    (h_step : (weightGrid, weightIdx, i', j') =
      bif isLeft then (z, i, i + 1, j) else (!z, j + o, i, j + 1))
    (hi : i' ≤ D.m) (hj : j' + o ≤ D.m) (h_zero : o = 0 ∨ i' = 0) :
    ParamsCorrespond (D.gridWeight weightGrid weightIdx (D.GridIndex z i j))
      (D.gridWeight weightGrid weightIdx (D.GridIndex z i' j'))
      (negIf isLeft (D.gridParam z o i j)) (negIf isLeft (D.gridParam z o i' j'))
      (D.gridSigns z o i j) (D.gridSigns z o i' j') := by
  cases isLeft <;> cases h_step
  · exact D.paramsCorrespond_grid_succ_right z o i j hi hj h_zero
  · obtain rfl : o = 0 := h_zero.resolve_right i.succ_ne_zero
    exact D.paramsCorrespond_grid_succ_left z i j hi hj

end Steps

/-- Adding the first block of an interval, for `i + j < m`: the node `(0, j)` with offset `i + 1`
and the node `(0, j + 1)` with offset `i` have corresponding negated parameters: at each infinite
place they satisfy the block rule `IsBlockRule` for the weight that is, at each end, the rank `N`
minus `D.gridWeight (!z) i`. -/
lemma paramsCorrespond_neg_gridParam_insert_first {j : ℕ} {P : Parameters} (D : Data P) {z : Bool}
    {i : ℕ} (hij : i + j < D.m) :
    ParamsCorrespond
      (fun τ : D.Φ ↦ card (D.GridIndex z 0 j) - D.gridWeight (!z) i (D.GridIndex z 0 j) τ)
      (fun τ : D.Φ ↦
        card (D.GridIndex z 0 (j + 1)) - D.gridWeight (!z) i (D.GridIndex z 0 (j + 1)) τ)
      (-D.gridParam z (i + 1) 0 j) (-D.gridParam z i 0 (j + 1))
      (D.gridSigns z (i + 1) 0 j) (D.gridSigns z i 0 (j + 1)) := by
  -- The signs at the offsets `i + 1` and `i` carry opposite common factors. So insert the block of
  -- `-w_(i+1)` on the opposite of the smaller space, and negate.
  suffices h_opposite : ParamsCorrespond (D.gridWeight (!z) i (D.GridIndex z 0 j))
      (D.gridWeight (!z) i (D.GridIndex z 0 (j + 1)))
      (D.gridParam z (i + 1) 0 j) (D.gridParam z i 0 (j + 1))
      (-D.gridSigns z (i + 1) 0 j) (D.gridSigns z i 0 (j + 1)) by
    simpa only [neg_neg] using h_opposite.neg
  intro τ
  have h_small : (D.gridCentres τ z).IsParam (gridBlocks (i + 1) 0 j) ((-1) ^ i)
      (toHCParam (-D.gridSigns z (i + 1) 0 j) (D.gridParam z (i + 1) 0 j τ)) := by
    simpa only [pow_succ, mul_neg_one, neg_neg] using
      (D.isParam_gridParam τ z (o := i + 1) (j := j) (by omega) (.inr rfl)).neg_signs
  have h_large : (D.gridCentres τ z).IsParam (gridBlocks i 0 (j + 1)) ((-1) ^ i)
      (D.gridParam z i 0 (j + 1) τ) := D.isParam_gridParam τ z (by omega) (.inr rfl)
  have h_centre : .inr i ∈ (D.gridCentres τ z).centres :=
    inr_mem_disjSum.2 (mem_range.2 (by omega))
  rw [gridWeight_not, gridWeight_not]
  exact h_small.isBlockRule_insert_of_down h_large
    (gridBlocks_succ_right_eq_insert_first i 0 j) (D.isSeparated_gridCentres τ z)
    (D.gridBlocks_subset τ z D.m.zero_le (by omega)) h_centre (by simp [gridBlocks])
    (D.mul_card_gridIndex_add_pow_three_le D.m.zero_le (by omega) D.m.zero_le (by omega)) rfl

/-- Adding or removing the first block of an interval, for `i + j < m`: the negated parameters of
the node `(0, j)` with offset `i + 1` and of the node `(0, j + 1)` with offset `i` correspond, in
both directions. -/
lemma paramsCorrespond_leftPair {j : ℕ} {P : Parameters} (D : Data P) {i : ℕ} (z : Bool)
    (hij : i + j < D.m) :
    ParamsCorrespond
        (fun τ : D.Φ ↦ card (D.GridIndex z 0 j) - D.gridWeight (!z) i (D.GridIndex z 0 j) τ)
        (fun τ : D.Φ ↦
          card (D.GridIndex z 0 (j + 1)) - D.gridWeight (!z) i (D.GridIndex z 0 (j + 1)) τ)
        (-D.gridParam z (i + 1) 0 j) (-D.gridParam z i 0 (j + 1))
        (D.gridSigns z (i + 1) 0 j) (D.gridSigns z i 0 (j + 1)) ∧
      ParamsCorrespond
        (fun τ : D.Φ ↦
          card (D.GridIndex z 0 (j + 1)) - D.gridWeight (!z) i (D.GridIndex z 0 (j + 1)) τ)
        (fun τ : D.Φ ↦ card (D.GridIndex z 0 j) - D.gridWeight (!z) i (D.GridIndex z 0 j) τ)
        (-D.gridParam z i 0 (j + 1)) (-D.gridParam z (i + 1) 0 j)
        (D.gridSigns z i 0 (j + 1)) (D.gridSigns z (i + 1) 0 j) :=
  ⟨D.paramsCorrespond_neg_gridParam_insert_first hij,
    (D.paramsCorrespond_neg_gridParam_insert_first hij).symm⟩

end New.Data

end
