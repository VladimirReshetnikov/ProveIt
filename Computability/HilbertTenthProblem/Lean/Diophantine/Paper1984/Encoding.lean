import Diophantine.Paper1984.Machine
import Diophantine.Paper1984.Compare

/-!
# Jones–Matijasevič 1984, §3: the system (24)–(39)

For a register machine program `P` (with `r` registers and lines `L0 … Ll`) and an
input `x`, the paper writes down conditions on the unknowns
`s, Q, I, R_1, …, R_r, L_0, …, L_l` which are solvable iff `P` accepts `x`:

* (24) `x + s < Q/2`, (25) `l + 1 < Q`, (26) `Q pow 2`, (27) `1 + (Q−1) I = Q^{s+1}`;
* (29) `R_j ≼ (Q/2 − 1) I`; (30) `I = Σ L_i`; (31) `L_i ≼ I`; (32) `1 ≼ L_0`; (33) `L_l = Q^s`;
* per line: (34) `Q L_i ≼ L_k` for `GO TO Lk`, the pair (36) for `IF Rj < Rm GO TO Lk`,
  the pair (37) for `IF Rj ≤ Rm GO TO Lk`, and `Q L_i ≼ L_{i+1}` for arithmetic lines;
  a constant `0`/`1` in a comparison has encoded history `0`/`I`;
* the register equations (38)/(39).

This file defines the system (`Sys`) and proves the bookkeeping lemmas shared by
the two directions of the main theorem (`Soundness.lean`, `Completeness.lean`).
-/

namespace JM1984
namespace RM

open Finset

variable {r : ℕ}

/-- The encoded history of an operand: `R_j` for a register, `0` and `I` for the constants. -/
def Operand.enc (I : ℕ) (R : Fin r → ℕ) : Operand r → ℕ
  | .reg j => R j
  | .zero => 0
  | .one => I

/-- The condition attached to line `i` carrying command `c`. -/
def lineCond (Q I : ℕ) (R : Fin r → ℕ) (L : ℕ → ℕ) (i : ℕ) : Cmd r → Prop
  | .goto k => Q * L i ≼ L k
  | .ifLt a b k => Q * L i ≼ L k + L (i + 1) ∧
      Q * L i ≼ L k + Q * I + 2 * a.enc I R - 2 * b.enc I R
  | .ifLe a b k => Q * L i ≼ L k + L (i + 1) ∧
      Q * L i ≼ L (i + 1) + Q * I + 2 * b.enc I R - 2 * a.enc I R
  | .arith _ => Q * L i ≼ L (i + 1)
  | .stop => True

/-- `δ_i(j)`: the change of register `j` prescribed by line `i` (`0` for non-arithmetic lines). -/
def delta (P : Program r) (i : ℕ) (j : Fin r) : ℤ :=
  match P[i]? with
  | some (.arith δ) => δ j
  | _ => 0

/-- The register equation (38)/(39) for register `j`, with the subtracted sum moved to the
left-hand side (the paper's equation is an identity of integers). -/
def regEq (P : Program r) (x Q : ℕ) (R : Fin r → ℕ) (L : ℕ → ℕ) (j : Fin r) : Prop :=
  R j + ∑ i ∈ range P.length, (if delta P i j = -1 then Q * L i else 0)
    = Q * R j + ∑ i ∈ range P.length, (if delta P i j = 1 then Q * L i else 0)
      + (if j.val = 0 then x else 0)

/-- The system (24)–(39) for program `P` and input `x`; `s, Q, I, R, L` are the unknowns. -/
structure Sys (P : Program r) (x s Q I : ℕ) (R : Fin r → ℕ) (L : ℕ → ℕ) : Prop where
  c24 : 2 * (x + s) < Q
  c25 : P.length < Q
  c26 : ∃ q, Q = 2 ^ q
  c27 : 1 + (Q - 1) * I = Q ^ (s + 1)
  c29 : ∀ j, R j ≼ (Q / 2 - 1) * I
  c30 : I = ∑ i ∈ range P.length, L i
  c31 : ∀ i < P.length, L i ≼ I
  c32 : 1 ≼ L 0
  c33 : L (P.length - 1) = Q ^ s
  lines : ∀ (i : ℕ) (c : Cmd r), P[i]? = some c → lineCond Q I R L i c
  regs : ∀ j, regEq P x Q R L j

/-! ### Bookkeeping lemmas -/

/-- (27) ⇔ (28): the number with all blocks `1`. -/
theorem geom_blocks {Q : ℕ} (hQ : 1 ≤ Q) (n : ℕ) :
    1 + (Q - 1) * blocks Q n (fun _ => 1) = Q ^ n := by
  obtain ⟨Q', rfl⟩ : ∃ Q', Q = Q' + 1 := ⟨Q - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [blocks_succ]
    calc 1 + Q' * (blocks (Q' + 1) n (fun _ => 1) + 1 * (Q' + 1) ^ n)
        = (1 + Q' * blocks (Q' + 1) n (fun _ => 1)) + Q' * (Q' + 1) ^ n := by ring
      _ = (Q' + 1) ^ n + Q' * (Q' + 1) ^ n := by rw [ih]
      _ = (Q' + 1) ^ (n + 1) := by ring

theorem two_pow_div_two {q : ℕ} (hq : 1 ≤ q) : 2 ^ q / 2 = 2 ^ (q - 1) := by
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  rw [pow_succ, Nat.mul_div_cancel _ (by norm_num), Nat.add_sub_cancel]

theorem two_mul_two_pow_div_two {q : ℕ} (hq : 1 ≤ q) : 2 * (2 ^ q / 2) = 2 ^ q := by
  rw [two_pow_div_two hq, ← pow_succ', Nat.sub_add_cancel hq]

theorem blocks_ite (Q n : ℕ) (c : Prop) [Decidable c] (f : ℕ → ℕ) :
    (if c then blocks Q n f else 0) = blocks Q n (fun t => if c then f t else 0) := by
  split_ifs <;> simp [blocks]

theorem blocks_const_zero (Q n : ℕ) : blocks Q n (fun _ => 0) = 0 := by simp [blocks]

theorem digit_eq_zero_of_lt {Q a n t : ℕ} (hQ : 0 < Q) (ha : a < Q ^ n) (ht : n ≤ t) :
    digit Q a t = 0 := by
  unfold digit
  rw [Nat.div_eq_of_lt (lt_of_lt_of_le ha (Nat.pow_le_pow_right hQ ht)), Nat.zero_mod]

/-- A sum of one-hot indicators over the lines, filtered by a predicate on the line. -/
theorem sum_ite_indicator {n i0 : ℕ} (hi0 : i0 < n) (p : ℕ → Prop) [DecidablePred p]
    (f : ℕ → ℕ) (hf : ∀ i, f i = if i = i0 then 1 else 0) :
    ∑ i ∈ range n, (if p i then f i else 0) = if p i0 then 1 else 0 := by
  rw [sum_eq_single i0]
  · rw [hf i0, if_pos rfl]
  · intro i _ hi
    rw [hf i, if_neg hi]
    simp
  · intro h
    exact absurd (mem_range.2 hi0) h

/-- If natural numbers sum to `1`, exactly one of them is `1` and the others are `0`. -/
theorem exists_unique_of_sum_eq_one {n : ℕ} {f : ℕ → ℕ} (h : ∑ i ∈ range n, f i = 1) :
    ∃ i0, i0 < n ∧ f i0 = 1 ∧ ∀ i < n, i ≠ i0 → f i = 0 := by
  have hne : ∑ i ∈ range n, f i ≠ 0 := by omega
  obtain ⟨i0, hi0, hf0⟩ := exists_ne_zero_of_sum_ne_zero hne
  have hle : f i0 ≤ 1 := by
    rw [← h]
    exact single_le_sum (fun _ _ => Nat.zero_le _) hi0
  have hf1 : f i0 = 1 := by omega
  refine ⟨i0, mem_range.1 hi0, hf1, fun i hi hne' => ?_⟩
  have := add_sum_erase (range n) f hi0
  rw [h, hf1] at this
  have hz : ∑ i ∈ (range n).erase i0, f i = 0 := by omega
  rw [sum_eq_zero_iff] at hz
  exact hz i (mem_erase.2 ⟨hne', mem_range.2 hi⟩)

/-- `Σ_i (if p i then Q·L_i else 0)` as a shifted block number. -/
theorem sum_ite_mul_blocks (Q m n : ℕ) (p : ℕ → Prop) [DecidablePred p] (f : ℕ → ℕ → ℕ) :
    ∑ i ∈ range n, (if p i then Q * blocks Q m (f i) else 0)
      = Q * blocks Q m (fun t => ∑ i ∈ range n, if p i then f i t else 0) := by
  rw [blocks_sum, mul_sum]
  apply sum_congr rfl
  intro i _
  rw [← blocks_ite]
  split_ifs <;> simp

theorem blocks_single_mul {Q n k c : ℕ} (hk : k < n) :
    blocks Q n (fun t => if t = k then c else 0) = c * Q ^ k := by
  unfold blocks
  rw [sum_eq_single k]
  · simp
  · intro t _ ht; simp [ht]
  · intro h; exact absurd (mem_range.2 hk) h

/-- A program with a normalised conditional jump has at least three lines. -/
theorem length_ge_three_of_cond {P : Program r} {i k : ℕ} (hk : k < P.length)
    (hki : k ≠ i) (hki1 : k ≠ i + 1) (hi : i + 1 < P.length) : 3 ≤ P.length := by
  omega

end RM
end JM1984
