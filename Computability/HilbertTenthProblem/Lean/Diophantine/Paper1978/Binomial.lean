import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic

/-!
# Jones 1978, Lemmas 2.5 and 2.6: binomial coefficients modulo `d` and partial binomials

* **Lemma 2.5.** For `d > 0`, if `a ≡ b (mod d)` then `C(a, z) ≡ C(b, z) (mod d/(d, z!))`.
* **Lemma 2.6.** For `z < N` and `N^z < X`, if `Y = ⌊(X+1)^N / X^z⌋` then
  `Y ≡ C(N, z) (mod X)`.

`⌊(X+1)^N / X^z⌋` is natural-number division `(X + 1) ^ N / X ^ z`.
-/

namespace Jones1978

open Finset

/-- `z! C(a, z) = a (a−1) ⋯ (a−z+1)` as integers (both sides vanish when `a < z`). -/
theorem cast_descFactorial (a z : ℕ) :
    (a.descFactorial z : ℤ) = ∏ j ∈ range z, ((a : ℤ) - j) := by
  rcases le_or_gt z a with h | h
  · rw [Nat.descFactorial_eq_prod_range]
    push_cast
    apply Finset.prod_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    rw [Nat.cast_sub (by omega)]
  · rw [Nat.descFactorial_eq_zero_iff_lt.2 h]
    push_cast
    symm
    apply Finset.prod_eq_zero (Finset.mem_range.2 h)
    simp

/-- Lemma 2.5. -/
theorem lemma_2_5 {d a b : ℕ} (hd : 0 < d) (h : a ≡ b [MOD d]) (z : ℕ) :
    a.choose z ≡ b.choose z [MOD d / Nat.gcd d z.factorial] := by
  -- `z! C(a,z) ≡ z! C(b,z) (mod d)` via `ZMod d`
  have key : z.factorial * a.choose z ≡ z.factorial * b.choose z [MOD d] := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose, ← Nat.descFactorial_eq_factorial_mul_choose,
      ← ZMod.natCast_eq_natCast_iff]
    have ha := cast_descFactorial a z
    have hb := cast_descFactorial b z
    have hab : ((a : ℕ) : ZMod d) = b := (ZMod.natCast_eq_natCast_iff _ _ _).2 h
    calc ((a.descFactorial z : ℕ) : ZMod d) = ((a.descFactorial z : ℤ) : ZMod d) := by simp
      _ = ∏ j ∈ range z, ((a : ZMod d) - j) := by rw [ha]; push_cast; rfl
      _ = ∏ j ∈ range z, ((b : ZMod d) - j) := by rw [hab]
      _ = ((b.descFactorial z : ℤ) : ZMod d) := by rw [hb]; push_cast; rfl
      _ = ((b.descFactorial z : ℕ) : ZMod d) := by simp
  exact Nat.ModEq.cancel_left_div_gcd hd key

/-- `∑_{m<z} N^m < N^z` for `N ≥ 2`. -/
theorem sum_pow_lt {N : ℕ} (hN : 2 ≤ N) (z : ℕ) : ∑ m ∈ range z, N ^ m < N ^ z := by
  induction z with
  | zero => simp
  | succ z ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have := Nat.mul_le_mul_left (N ^ z) hN
    omega

/-- The binomial expansion split at `z`: `(X+1)^N = Q X^z + v` with `c v < X^z` and
`Q ≡ C(N, z) (mod X)`, for `z < N` and `c N^z < X` (`c ≥ 1`). -/
theorem binomial_split_c {N z X c : ℕ} (hc : 0 < c) (hz : z < N) (hX : c * N ^ z < X) :
    ∃ Q v, (X + 1) ^ N = Q * X ^ z + v ∧ c * v < X ^ z ∧ Q ≡ N.choose z [MOD X] := by
  have hexp : (X + 1) ^ N = ∑ m ∈ range (N + 1), X ^ m * N.choose m := by
    have h := add_pow X 1 N
    simp only [one_pow, mul_one, Nat.cast_id] at h
    exact h
  have hsplit : ∑ m ∈ range (N + 1), X ^ m * N.choose m =
      ∑ m ∈ range z, X ^ m * N.choose m + ∑ m ∈ Ico z (N + 1), X ^ m * N.choose m :=
    (Finset.sum_range_add_sum_Ico _ (by omega)).symm
  refine ⟨∑ m ∈ Ico z (N + 1), X ^ (m - z) * N.choose m, ∑ m ∈ range z, X ^ m * N.choose m,
    ?_, ?_, ?_⟩
  · rw [hexp, hsplit, add_comm, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mem_Ico] at hm
    rw [mul_right_comm, ← pow_add, Nat.sub_add_cancel hm.1]
  · rcases Nat.eq_zero_or_pos z with rfl | hz0
    · simp
    have hN2 : 2 ≤ N := by omega
    have hX1 : 1 ≤ X := by
      have : 1 ≤ N ^ z := Nat.one_le_pow _ _ (by omega)
      nlinarith
    have hS : c * ∑ m ∈ range z, N.choose m < X := by
      calc c * ∑ m ∈ range z, N.choose m ≤ c * ∑ m ∈ range z, N ^ m :=
            Nat.mul_le_mul_left _ (Finset.sum_le_sum (fun m _ => Nat.choose_le_pow N m))
        _ < c * N ^ z := Nat.mul_lt_mul_of_pos_left (sum_pow_lt hN2 z) hc
        _ < X := hX
    calc c * ∑ m ∈ range z, X ^ m * N.choose m
        ≤ c * ∑ m ∈ range z, X ^ (z - 1) * N.choose m := by
          apply Nat.mul_le_mul_left
          apply Finset.sum_le_sum
          intro m hm
          rw [Finset.mem_range] at hm
          exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hX1 (by omega))
      _ = X ^ (z - 1) * (c * ∑ m ∈ range z, N.choose m) := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro m _
          ring
      _ < X ^ (z - 1) * X := Nat.mul_lt_mul_of_pos_left hS (by positivity)
      _ = X ^ z := by rw [← pow_succ, Nat.sub_add_cancel hz0]
  · rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : z < N + 1), Nat.sub_self, pow_zero, one_mul]
    have : ∑ m ∈ Ico (z + 1) (N + 1), X ^ (m - z) * N.choose m =
        X * ∑ m ∈ Ico (z + 1) (N + 1), X ^ (m - z - 1) * N.choose m := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.mem_Ico] at hm
      rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel (by omega)]
    rw [this]
    show (N.choose z + X * _) % X = N.choose z % X
    rw [Nat.add_mul_mod_self_left]

theorem binomial_split' {N z X : ℕ} (hz : z < N) (hX : N ^ z < X) :
    ∃ Q v, (X + 1) ^ N = Q * X ^ z + v ∧ v < X ^ z ∧ Q ≡ N.choose z [MOD X] := by
  obtain ⟨Q, v, h1, h2, h3⟩ := binomial_split_c one_pos hz (by simpa using hX)
  exact ⟨Q, v, h1, by simpa using h2, h3⟩

/-- The quotient and remainder of `(X+1)^N` by `X^z`: `(X+1)^N = ⌊(X+1)^N/X^z⌋ X^z + v`
with `c v < X^z` when `c N^z < X`. -/
theorem partial_binomial_rem {N z X c : ℕ} (hc : 0 < c) (hz : z < N) (hX : c * N ^ z < X) :
    ∃ v, (X + 1) ^ N = (X + 1) ^ N / X ^ z * X ^ z + v ∧ c * v < X ^ z := by
  obtain ⟨Q, v, h1, h2, -⟩ := binomial_split_c hc hz hX
  have hpos : 0 < X ^ z := by
    have : 0 < X := by
      have : 1 ≤ N ^ z := Nat.one_le_pow _ _ (by omega)
      nlinarith
    positivity
  have hQ : (X + 1) ^ N / X ^ z = Q := by
    rw [h1, add_comm, mul_comm, Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt (by nlinarith),
      zero_add]
  rw [hQ]
  exact ⟨v, h1, h2⟩

/-- Lemma 2.6. -/
theorem lemma_2_6 {z N X : ℕ} (hz : z < N) (hX : N ^ z < X) :
    (X + 1) ^ N / X ^ z ≡ N.choose z [MOD X] := by
  obtain ⟨Q, v, hQ, hv, hc⟩ := binomial_split' hz hX
  have hpos : 0 < X ^ z := by omega
  rw [hQ, add_comm, mul_comm, Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hv, zero_add]
  exact hc

/-- `⌊(X+1)^N / X^z⌋ ≥ X^(N−z)`. -/
theorem pow_le_partial_binomial {z N X : ℕ} (hz : z ≤ N) (hX : 0 < X) :
    X ^ (N - z) ≤ (X + 1) ^ N / X ^ z := by
  rw [← Nat.pow_div hz hX]
  exact Nat.div_le_div_right (Nat.pow_le_pow_left (Nat.le_succ X) N)

end Jones1978
