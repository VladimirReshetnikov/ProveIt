/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.ProgressionPartitionComposition
import OAI.Combinatorics.Progressions.Estimates.SimultaneousDirichlet

namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {ι : Type*} [Fintype ι]

theorem periodic_lipschitz_dist_le_of_integer_approx
    {F : (ι → ℝ) → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F)
    (hperiod : ∀ x : ι → ℝ, ∀ m : ι → ℤ, F (fun i => x i + m i) = F x)
    (x y : ι → ℝ) (m : ι → ℤ) {ε : ℝ} (hε : 0 ≤ ε)
    (hclose : ∀ i, |x i - (y i + m i)| ≤ ε) :
    dist (F x) (F y) ≤ L * ε := by
  have hdist : dist x (fun i => y i + m i) ≤ ε := by
    apply (dist_pi_le_iff hε).mpr
    intro i
    simpa only [Real.dist_eq] using hclose i
  have h := hF.dist_le_mul x (fun i => y i + m i)
  rw [hperiod] at h
  exact h.trans (mul_le_mul_of_nonneg_left hdist L.coe_nonneg)

omit [Fintype ι] in
theorem affine_phase_block_error {N q H Q : ℕ} (hq : 0 < q)
    (hH : 0 < H) (hQ : 0 < Q) (alpha beta : ι → ℝ) (m : ι → ℤ)
    (happrox : ∀ i, |(q : ℝ) * alpha i - m i| ≤ 1 / (Q : ℝ))
    (n : Fin N) (i : ι) :
    |((n.val : ℝ) * alpha i + beta i) -
      (((progressionBlockStart (progressionBlockLabel q H hq n) : ℕ) : ℝ) * alpha i +
        beta i + ((n.val / q % H : ℕ) : ℝ) * m i)| ≤ (H : ℝ) / Q := by
  have hn : (n.val : ℝ) =
      (progressionBlockStart (progressionBlockLabel q H hq n) : ℝ) +
        (q : ℝ) * (n.val / q % H : ℕ) := by
    exact_mod_cast (progressionBlock_reconstruct (H := H) hq n).symm
  have hoff : ((n.val / q % H : ℕ) : ℝ) ≤ H := by
    exact_mod_cast (Nat.mod_lt (n.val / q) hH).le
  calc
    _ = |((n.val / q % H : ℕ) : ℝ) * ((q : ℝ) * alpha i - m i)| := by
      congr 1
      rw [hn]
      ring
    _ = ((n.val / q % H : ℕ) : ℝ) * |(q : ℝ) * alpha i - m i| := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    _ ≤ ((n.val / q % H : ℕ) : ℝ) * (1 / (Q : ℝ)) :=
      mul_le_mul_of_nonneg_left (happrox i) (Nat.cast_nonneg _)
    _ ≤ (H : ℝ) * (1 / (Q : ℝ)) :=
      mul_le_mul_of_nonneg_right hoff (by positivity)
    _ = _ := by ring

theorem affine_torus_block_error {N q H Q : ℕ} (hq : 0 < q)
    (hH : 0 < H) (hQ : 0 < Q) (alpha beta : ι → ℝ) (m : ι → ℤ)
    (happrox : ∀ i, |(q : ℝ) * alpha i - m i| ≤ 1 / (Q : ℝ))
    {F : (ι → ℝ) → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F)
    (hperiod : ∀ x : ι → ℝ, ∀ m : ι → ℤ, F (fun i => x i + m i) = F x)
    (n : Fin N) :
    dist (F (fun i => (n.val : ℝ) * alpha i + beta i))
      (F (fun i => (progressionBlockStart (progressionBlockLabel q H hq n) : ℝ) *
        alpha i + beta i)) ≤ L * ((H : ℝ) / Q) := by
  apply periodic_lipschitz_dist_le_of_integer_approx hF hperiod
    _ _ (fun i => (n.val / q % H : ℕ) * m i) (by positivity)
  intro i
  simpa only [Int.cast_mul, Int.cast_natCast] using
    affine_phase_block_error hq hH hQ alpha beta m happrox n i

theorem exists_affine_torus_progression_partition {N H : ℕ} (hH : 0 < H)
    (hsize : H ^ (2 * Fintype.card ι + 1) ≤ N) (alpha beta : ι → ℝ)
    {F : (ι → ℝ) → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F)
    (hperiod : ∀ x : ι → ℝ, ∀ m : ι → ℤ, F (fun i => x i + m i) = F x) :
    ∃ q : ℕ, ∃ hq : 0 < q, q ≤ H ^ (2 * Fintype.card ι) ∧
      Fintype.card (Fin q × Fin (N / q / H + 1)) * H ≤ 2 * N ∧
      ∀ n : Fin N,
        dist (F (fun i => (n.val : ℝ) * alpha i + beta i))
          (F (fun i => (progressionBlockStart (progressionBlockLabel q H hq n) : ℝ) *
            alpha i + beta i)) ≤ (L : ℝ) / H := by
  obtain ⟨q, hq, hqbound, m, hm⟩ := simultaneous_dirichlet alpha (H ^ 2) (pow_pos hH _)
  rw [← pow_mul] at hqbound
  have hfit : q * H ≤ N := by
    calc
      _ ≤ H ^ (2 * Fintype.card ι) * H := Nat.mul_le_mul_right H hqbound
      _ = H ^ (2 * Fintype.card ι + 1) := (pow_succ _ _).symm
      _ ≤ N := hsize
  refine ⟨q, hq, hqbound, progressionBlock_label_count_mul_le_twice hfit, ?_⟩
  intro n
  have h := affine_torus_block_error hq hH (pow_pos hH 2) alpha beta m hm hF hperiod n
  have hHR : (H : ℝ) ≠ 0 := by exact_mod_cast hH.ne'
  convert h using 1
  push_cast
  field_simp

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem affine_torus_density_increment {ι : Type*} [Fintype ι]
    {N H : ℕ} (hH : 0 < H) (hsize : H ^ (2 * Fintype.card ι + 1) ≤ N)
    (alpha beta : ι → ℝ) (f : ℕ → ℝ) {F : (ι → ℝ) → ℝ} {L : ℝ≥0}
    (hF : LipschitzWith L F)
    (hperiod : ∀ x : ι → ℝ, ∀ m : ι → ℤ, F (fun i => x i + m i) = F x)
    (hF01 : ∀ x, F x ∈ Set.Icc (0 : ℝ) 1)
    (hf : ∀ n < N, f n ∈ Set.Icc (0 : ℝ) 1)
    {b σ : ℝ} (hb : b ∈ Set.Icc (0 : ℝ) 1) (hσ : 0 < σ)
    (hsmall : 4 * (L : ℝ) ≤ σ * H)
    (hscore : σ ≤ 𝔼 n : Fin N,
      (f n.val - b) * F (fun i => (n.val : ℝ) * alpha i + beta i)) :
    ∃ q a len : ℕ, 0 < q ∧ q ≤ H ^ (2 * Fintype.card ι) ∧
      σ * H / 4 ≤ len ∧ len ≤ H ∧
      (∀ j < len, a + q * j < N) ∧
      b < 𝔼 j : Fin len, f (a + q * j.val) := by
  have hN : 0 < N := (pow_pos hH _).trans_le hsize
  let : NeZero N := ⟨hN.ne'⟩
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  obtain ⟨q, hq, hqbound, hcount, hosc⟩ :=
    exists_affine_torus_progression_partition hH hsize alpha beta hF hperiod
  let cell := progressionBlockLabel (N := N) q H hq
  let B (n : Fin N) := F (fun i => (n.val : ℝ) * alpha i + beta i)
  let c (i : Fin q × Fin (N / q / H + 1)) :=
    F (fun j => (progressionBlockStart i : ℝ) * alpha j + beta j)
  have hcountR : (Fintype.card (Fin q × Fin (N / q / H + 1)) : ℝ) * H ≤ 2 * N := by
    exact_mod_cast hcount
  have hcost : (Fintype.card (Fin q × Fin (N / q / H + 1)) : ℝ) *
      (σ * H / 4) / N ≤ σ / 2 := by
    apply (div_le_iff₀ hNR).mpr
    nlinarith [mul_le_mul_of_nonneg_left hcountR hσ.le]
  have hoscSmall : (L : ℝ) / H ≤ σ / 4 := by
    apply (div_le_iff₀ hHR).mpr
    nlinarith
  obtain ⟨i, hlarge, hdense⟩ := exists_large_cell_of_normalized_score cell
    (fun n => f n.val) B c (b := b) (ω := (L : ℝ) / H) (σ := σ)
    (σ * H / 4) (by positivity) (fun n => hf n.val n.isLt) hb
    (fun n => hF01 _) (fun i => (hF01 _).1) (by positivity)
    (fun n => by simpa only [B, c, cell, Real.dist_eq] using hosc n)
    hscore (by simp only [Fintype.card_fin]; linarith)
  let len := truncatedProgressionLength N (progressionBlockStart i) q H
  refine ⟨q, progressionBlockStart i, len, hq, hqbound, ?_, ?_, ?_, ?_⟩
  · simpa only [cell, progressionBlock_card hq hH] using hlarge
  · by_cases ha : progressionBlockStart i < N
    · simpa only [len, truncatedProgressionLength, ite_eq_left ha] using
        (min_le_left H ((N - 1 - progressionBlockStart i) / q + 1))
    · simp only [len, truncatedProgressionLength, ite_eq_right ha, Nat.zero_le]
  · intro j hj
    exact ((lt_truncatedProgressionLength_iff hq).mp hj).2
  · simpa only [cell, progressionBlock_expect hq hH] using hdense

end Erdos3

end

end OAI
