/-
Adapted from openai/math, revision adc7f1241b42e322a6451854ab7e4b4c146bf78a:
lean/OAI/Combinatorics/Progressions/Polynomial/PolynomialCoordinatePartition.lean,
PolynomialCoordinatePartitionBound and its zero, step, and existence proofs.
Copyright remains with the respective upstream copyright holders; OpenAI is
identified as publisher, with no individualized copyright notice upstream.
SPDX-License-Identifier: Apache-2.0
See the adjacent LICENSE.openai-math for provenance and the full license.

Modified for ProveIt (2026-10-08): strengthen the average-length guarantee to
an individual lower bound on every cell, replace truncated residue blocks
with comparable residue progressions, perform degree reduction at twice
the induction scale, and increase the degree-dependent exponent constant.
-/
import OAI.Combinatorics.Progressions.Polynomial.PolynomialCoordinatePartition
import OAI.Combinatorics.Progressions.Lattices.ComparableResidueProgressionPartition

/-! A simultaneous polynomial partition with no short tail cells.

For each degree k there are constants K >= 2 and p > 0 such that d real
polynomials of degree at most k on an interval of length
N >= H^(p*(d+1)^(2*k)), with H >= K*(d+1), admit a progression partition
whose every cell has length at least H. On each cell, each polynomial is
within k/H of a fixed real constant modulo an integer.

The residue blocks have lengths in [T, 2*T); the induction is applied to
each actual block length. This avoids the short tails introduced by
restricting a partition of T. Constants are existential. The theorem is
one-dimensional and does not establish the multilinear-box conclusion
of Gowers's Lemma 16.1.
-/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open OAI.Erdos3 Polynomial
universe u
def MinimumPolynomialPartitionBound (k : ℕ) (K : ℝ) (p : ℕ) : Prop :=
  ∀ (ι : Type u) [Fintype ι] (P : ι → Polynomial ℝ),
    (∀ i, (P i).natDegree ≤ k) → ∀ (N H : ℕ), 0 < H →
    K * ((Fintype.card ι : ℝ) + 1) ≤ H →
    H ^ (p * (Fintype.card ι + 1) ^ (2 * k)) ≤ N →
    ∃ (Q : FiniteProgressionPartition N) (z : Q.Label → ι → ℝ) (m : Q.Label → ℕ → ι → ℤ),
      (∀ i, H ≤ Q.length i) ∧
      ∀ i n, n < Q.length i → ∀ j,
        |(P j).eval ((Q.start i + Q.step i * n : ℕ) : ℝ) - m i n j - z i j| ≤ (k : ℝ) / H

theorem minimumPolynomialPartitionBound_zero : MinimumPolynomialPartitionBound.{u} 0 2 1 := by
  intro ι _ P hP N H hH hscale hsize
  have hHN : H ≤ N := by simpa using hsize
  refine ⟨FiniteProgressionPartition.whole N, (fun _ j => (P j).coeff 0), (fun _ _ _ => 0), ?_, ?_⟩
  · intro i
    exact hHN
  · intro i n hn j
    have heq (x : ℝ) : (P j).eval x = (P j).coeff 0 := by
      simpa only [eval_C] using congrArg (fun Q : Polynomial ℝ => Q.eval x)
        (eq_C_of_natDegree_le_zero (hP j))
    rw [heq]
    simp

theorem MinimumPolynomialPartitionBound.step {k p C e : ℕ} {K : ℝ}
    (hK : 2 ≤ K) (hp : 0 < p) (hpartition : MinimumPolynomialPartitionBound.{u} k K p)
    (hW : PolynomialIntervalPowerBound (k + 1) C e) :
    MinimumPolynomialPartitionBound.{u} (k + 1) (max K (schmidtRecurrenceBase C e))
      (p * (2 * (k + 3) * schmidtRecurrenceExponent e + 1)) := by
  intro ι _ P hP N H hH hscale hsize
  let d := Fintype.card ι
  let r := p * (d + 1) ^ (2 * k)
  let T := H ^ r
  have hr : 0 < r := Nat.mul_pos hp (pow_pos (by omega : 0 < d + 1) _)
  have hT : 0 < T := pow_pos hH _
  have hHT : H ≤ T := by
    simpa only [pow_one] using (show H ^ 1 ≤ H ^ r from pow_le_pow_right₀ (by omega) (by omega))
  have hscaleK : K * ((Fintype.card ι : ℝ) + 1) ≤ H :=
    (mul_le_mul_of_nonneg_right (le_max_left K _) (by positivity)).trans hscale
  have hscaleW : schmidtRecurrenceBase C e * ((Fintype.card ι : ℝ) + 1) ≤ ((2 * T : ℕ) : ℝ) := by
    have h := (mul_le_mul_of_nonneg_right (le_max_right K _) (by positivity)).trans hscale
    exact h.trans (by exact_mod_cast (hHT.trans (by omega : T ≤ 2 * T)))
  have hH2 : 2 ≤ H := by
    have hc : (1 : ℝ) ≤ (Fintype.card ι : ℝ) + 1 := by norm_num
    have h : (2 : ℝ) ≤ H := hK.trans ((le_mul_of_one_le_right (by linarith : 0 ≤ K) hc).trans hscaleK)
    exact_mod_cast h
  have hT2 : 2 ≤ T := hH2.trans hHT
  have hsizeT : T ^ ((2 * (k + 3) * schmidtRecurrenceExponent e * (d + 1) ^ 2) + 1) ≤ N := by
    apply le_trans _ hsize
    change (H ^ r) ^ _ ≤ H ^ _
    rw [← pow_mul]
    exact pow_le_pow_right₀ (by omega) (by
      convert polynomial_partition_exponent_step k p (2 * schmidtRecurrenceExponent e) d using 1 <;> ring)
  obtain ⟨q, hq, hqbound, top, hreduce⟩ := hW.polynomial_coordinate_reduction P hP (2 * T) (by omega) hscaleW
  have hqbound' : q ≤ T ^ (2 * (k + 3) * schmidtRecurrenceExponent e * (d + 1) ^ 2) := by
    apply hqbound.trans
    calc
      (2 * T) ^ _ ≤ (T ^ 2) ^ _ := Nat.pow_le_pow_left (by nlinarith : 2 * T ≤ T ^ 2) _
      _ = _ := by rw [← pow_mul]; congr 1; ring
  have hfit : q * T ≤ N := by
    calc
      _ ≤ T ^ (2 * (k + 3) * schmidtRecurrenceExponent e * (d + 1) ^ 2) * T :=
        Nat.mul_le_mul_right T hqbound'
      _ = T ^ ((2 * (k + 3) * schmidtRecurrenceExponent e * (d + 1) ^ 2) + 1) := (pow_succ _ _).symm
      _ ≤ N := hsizeT
  let B := FiniteProgressionPartition.comparableResidueProgressions N q T hq hT hfit
  have hBlength (i : B.Label) : T ≤ B.length i ∧ B.length i < 2 * T :=
    FiniteProgressionPartition.comparableResidueProgressions_length_bounds N q T hq hT hfit i
  have hBstep (i : B.Label) : B.step i = q :=
    FiniteProgressionPartition.comparableResidueProgressions_step N q T hq hT hfit i
  choose R hRdegree hRerror using (fun i : B.Label => hreduce (B.start i : ℝ))
  have hlocal (i : B.Label) := hpartition ι (R i) (hRdegree i) (B.length i) H hH hscaleK (hBlength i).1
  choose Q z m hQlength hQerror using hlocal
  let child := Q
  let result := B.bind child
  let index (i : result.Label) (n : ℕ) := (child i.1).start i.2 + (child i.1).step i.2 * n
  let integers (i : result.Label) (n : ℕ) (j : ι) : ℤ :=
    top j * (index i n : ℤ) ^ (k + 1) + m i.1 i.2 n j
  refine ⟨result, (fun i => z i.1 i.2), integers, ?_, ?_⟩
  · rintro ⟨i, j⟩
    exact hQlength i j
  · rintro ⟨i, j⟩ n hn a
    let s := index ⟨i, j⟩ n
    have hsB : s < B.length i := (child i).point_lt j hn
    have hsT : s < 2 * T := hsB.trans (hBlength i).2
    have houter := hRerror i s hsT a
    have hnQ : n < (Q i).length j := hn
    have hinner := hQerror i j n hnQ a
    change |(R i a).eval (s : ℝ) - m i j n a - z i j a| ≤ (k : ℝ) / H at hinner
    have hindex : result.start ⟨i, j⟩ + result.step ⟨i, j⟩ * n = B.start i + q * s := by
      change (B.start i + B.step i * (child i).start j) + (B.step i * (child i).step j) * n = _
      rw [hBstep]
      dsimp [s, index]
      ring
    rw [hindex]
    have houter' : |(P a).eval ((B.start i + q * s : ℕ) : ℝ) -
        ((R i a).eval (s : ℝ) + ((top a * (s : ℤ) ^ (k + 1) : ℤ) : ℝ))| ≤ 1 / ((2 * T : ℕ) : ℝ) := by
      simpa only [Nat.cast_add, Nat.cast_mul] using houter
    have hid : (P a).eval ((B.start i + q * s : ℕ) : ℝ) - integers ⟨i, j⟩ n a - z i j a =
        ((P a).eval ((B.start i + q * s : ℕ) : ℝ) -
          ((R i a).eval (s : ℝ) + ((top a * (s : ℤ) ^ (k + 1) : ℤ) : ℝ))) +
        ((R i a).eval (s : ℝ) - m i j n a - z i j a) := by
      dsimp [integers, s]
      push_cast
      ring
    rw [hid]
    calc
      _ ≤ |(P a).eval ((B.start i + q * s : ℕ) : ℝ) -
          ((R i a).eval (s : ℝ) + ((top a * (s : ℤ) ^ (k + 1) : ℤ) : ℝ))| +
          |(R i a).eval (s : ℝ) - m i j n a - z i j a| := abs_add_le _ _
      _ ≤ 1 / ((2 * T : ℕ) : ℝ) + (k : ℝ) / H := add_le_add houter' hinner
      _ ≤ _ := by simpa only [mul_one] using polynomial_partition_error_step k (by norm_num : (0 : ℝ) ≤ 1) hH (hHT.trans (by omega : T ≤ 2 * T))

theorem exists_minimum_polynomial_partition_bound (k : ℕ) :
    ∃ (K : ℝ) (p : ℕ), 2 ≤ K ∧ 0 < p ∧ MinimumPolynomialPartitionBound.{u} k K p := by
  induction k with
  | zero => exact ⟨2, 1, le_rfl, by decide, minimumPolynomialPartitionBound_zero⟩
  | succ k ih =>
    obtain ⟨K, p, hK, hp, hpartition⟩ := ih
    obtain ⟨C, e, hC, he, hW⟩ := polynomial_weyl_inverse_power_interval k
    exact ⟨max K (schmidtRecurrenceBase C e), p * (2 * (k + 3) * schmidtRecurrenceExponent e + 1),
      hK.trans (le_max_left _ _), Nat.mul_pos hp (by omega), hpartition.step hK hp hW⟩

end LeanProofs.GowersSzemeredi
