import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Pi

namespace OAI

section

namespace Erdos3

noncomputable def uniformIntervalGrid (B : ℝ) (N : ℕ) (k : Fin (N + 1)) : ℝ :=
  -B + (2 * B / N) * k

theorem uniformIntervalGrid_mem {B : ℝ} (hB : 0 ≤ B) {N : ℕ} (hN : 0 < N)
    (k : Fin (N + 1)) : |uniformIntervalGrid B N k| ≤ B := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hk : (k : ℝ) ≤ N := by exact_mod_cast Nat.le_of_lt_succ k.isLt
  have hstep : 0 ≤ 2 * B / N := by positivity
  have htop : (2 * B / N) * N = 2 * B := div_mul_cancel₀ _ hNr.ne'
  have hle := mul_le_mul_of_nonneg_left hk hstep
  apply abs_le.mpr
  dsimp [uniformIntervalGrid]
  constructor
  · have := mul_nonneg hstep (Nat.cast_nonneg k.val)
    linarith
  · linarith

theorem exists_uniformIntervalGrid_approx {B : ℝ} (hB : 0 < B) {N : ℕ} (hN : 0 < N)
    (x : ℝ) (hx : |x| ≤ B) :
    ∃ k : Fin (N + 1), |x - uniformIntervalGrid B N k| ≤ 2 * B / N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  let δ : ℝ := 2 * B / N
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδN : δ * N = 2 * B := div_mul_cancel₀ _ hNr.ne'
  let q : ℝ := (x + B) / δ
  have hq0 : 0 ≤ q := div_nonneg (by linarith [(abs_le.mp hx).1]) hδ.le
  have hqN : q ≤ N := by
    apply (div_le_iff₀ hδ).mpr
    linarith [(abs_le.mp hx).2]
  let k : Fin (N + 1) := ⟨⌊q⌋₊, Nat.lt_succ_of_le (Nat.floor_le_of_le hqN)⟩
  refine ⟨k, ?_⟩
  have hq : δ * q = x + B := by dsimp [q]; field_simp
  have heq : x - uniformIntervalGrid B N k = δ * (q - ⌊q⌋₊) := by
    change x - (-B + δ * (⌊q⌋₊ : ℝ)) = _
    rw [mul_sub, hq]
    ring
  rw [heq, abs_mul, abs_of_pos hδ]
  exact (mul_le_mul_of_nonneg_left (Nat.abs_sub_floor_le hq0) hδ.le).trans_eq (mul_one δ)

noncomputable def uniformBoxGrid {ι : Type*} (B : ℝ) (N : ℕ) (k : ι → Fin (N + 1)) : ι → ℝ :=
  fun i => uniformIntervalGrid B N (k i)

theorem uniformBoxGrid_mem {ι : Type*} {B : ℝ} (hB : 0 ≤ B) {N : ℕ} (hN : 0 < N)
    (k : ι → Fin (N + 1)) (i : ι) : |uniformBoxGrid B N k i| ≤ B :=
  uniformIntervalGrid_mem hB hN (k i)

theorem exists_uniformBoxGrid_approx {ι : Type*} [Fintype ι] {B : ℝ} (hB : 0 < B)
    {N : ℕ} (hN : 0 < N) (v : ι → ℝ) (hv : ∀ i, |v i| ≤ B) :
    ∃ k : ι → Fin (N + 1), dist v (uniformBoxGrid B N k) ≤ 2 * B / N := by
  classical
  choose k hk using fun i => exists_uniformIntervalGrid_approx hB hN (v i) (hv i)
  refine ⟨k, ?_⟩
  apply (dist_pi_le_iff (by positivity : (0 : ℝ) ≤ 2 * B / N)).mpr
  intro i
  simpa only [Real.dist_eq, uniformBoxGrid] using hk i

theorem uniformBoxGrid_card (ι : Type*) [Fintype ι] [DecidableEq ι] (N : ℕ) :
    Fintype.card (ι → Fin (N + 1)) = (N + 1) ^ Fintype.card ι := by simp

end Erdos3

end

section

namespace Erdos3

noncomputable def normalizedRealBoxGrid {σ : Type*} (T : σ → ℝ) (M : ℕ)
    (j : σ → Fin (M + 1)) : σ → ℝ :=
  fun i => T i * uniformBoxGrid 1 M j i

theorem normalizedRealBoxGrid_bound {σ : Type*} (T : σ → ℝ)
    (hT : ∀ i, 0 < T i) {M : ℕ} (hM : 0 < M)
    (j : σ → Fin (M + 1)) (i : σ) :
    |normalizedRealBoxGrid T M j i| ≤ T i := by
  rw [normalizedRealBoxGrid, abs_mul, abs_of_pos (hT i)]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (uniformBoxGrid_mem (by norm_num : (0 : ℝ) ≤ 1) hM j i) (hT i).le

theorem exists_normalizedRealBoxGrid_cell {σ : Type*} [Fintype σ]
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M : ℕ} (hM : 0 < M)
    (v : σ → ℝ) (hv : ∀ i, |v i| ≤ T i) :
    ∃ j : σ → Fin (M + 1), ∀ i,
      |v i - normalizedRealBoxGrid T M j i| ≤ T i * (2 / M) := by
  have hnorm (i : σ) : |v i / T i| ≤ 1 := by
    rw [abs_div, abs_of_pos (hT i)]
    exact (div_le_one (hT i)).mpr (hv i)
  obtain ⟨j, hj⟩ := exists_uniformBoxGrid_approx
    (by norm_num : (0 : ℝ) < 1) hM (fun i => v i / T i) hnorm
  refine ⟨j, fun i => ?_⟩
  have hji : |v i / T i - uniformBoxGrid 1 M j i| ≤ 2 / M := by
    simpa only [Real.dist_eq, mul_one] using
      (dist_le_pi_dist (fun i => v i / T i) (uniformBoxGrid 1 M j) i).trans hj
  calc
    _ = T i * |v i / T i - uniformBoxGrid 1 M j i| := by
      rw [show T i * |v i / T i - uniformBoxGrid 1 M j i| =
        |T i * (v i / T i - uniformBoxGrid 1 M j i)| by
          rw [abs_mul, abs_of_pos (hT i)]]
      congr 1
      dsimp only [normalizedRealBoxGrid]
      field_simp [(hT i).ne']
    _ ≤ _ := mul_le_mul_of_nonneg_left hji (hT i).le

end Erdos3

end

section

namespace Erdos3

theorem exists_uniformIntervalGrid_half_approx {B : ℝ} (hB : 0 < B)
    {N : ℕ} (hN : 0 < N) (x : ℝ) (hx : |x| ≤ B) :
    ∃ k : Fin (N + 1), |x - uniformIntervalGrid B N k| ≤ B / N := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  let δ : ℝ := 2 * B / N
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδN : δ * N = 2 * B := div_mul_cancel₀ _ hNr.ne'
  let q : ℝ := (x + B) / δ
  have hq0 : 0 ≤ q := div_nonneg (by linarith [(abs_le.mp hx).1]) hδ.le
  have hqN : q ≤ N := by
    apply (div_le_iff₀ hδ).mpr
    linarith [(abs_le.mp hx).2]
  let k : Fin (N + 1) := ⟨⌊q + 1 / 2⌋₊, (Nat.floor_lt (by positivity)).mpr (by
    push_cast
    linarith)⟩
  have hk : |q - (k.val : ℝ)| ≤ 1 / 2 := by
    apply abs_le.mpr
    have hlo := Nat.floor_le (show 0 ≤ q + 1 / 2 by positivity)
    have hhi := Nat.lt_floor_add_one (q + 1 / 2)
    change -(1 / 2) ≤ q - (⌊q + 1 / 2⌋₊ : ℝ) ∧ _
    constructor <;> linarith
  refine ⟨k, ?_⟩
  have heq : x - uniformIntervalGrid B N k = δ * (q - k.val) := by
    have hδq : δ * q = x + B := by dsimp [q]; field_simp
    change x - (-B + δ * k.val) = _
    rw [mul_sub, hδq]
    ring
  rw [heq, abs_mul, abs_of_pos hδ]
  exact (mul_le_mul_of_nonneg_left hk hδ.le).trans_eq (by dsimp [δ]; ring)

theorem exists_normalizedRealBoxGrid_half_cell {σ : Type*}
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {N : ℕ} (hN : 0 < N)
    (v : σ → ℝ) (hv : ∀ i, |v i| ≤ T i) :
    ∃ j : σ → Fin (N + 1), ∀ i,
      |v i - normalizedRealBoxGrid T N j i| ≤ T i / N := by
  classical
  have hnorm (i : σ) : |v i / T i| ≤ 1 := by
    rw [abs_div, abs_of_pos (hT i)]
    exact (div_le_one (hT i)).mpr (hv i)
  choose j hj using fun i => exists_uniformIntervalGrid_half_approx
    (by norm_num : (0 : ℝ) < 1) hN (v i / T i) (hnorm i)
  refine ⟨j, fun i => ?_⟩
  have heq : v i - normalizedRealBoxGrid T N j i =
      T i * (v i / T i - uniformIntervalGrid 1 N (j i)) := by
    dsimp only [normalizedRealBoxGrid, uniformBoxGrid]
    field_simp [(hT i).ne']
  rw [heq, abs_mul, abs_of_pos (hT i)]
  exact (mul_le_mul_of_nonneg_left (hj i) (hT i).le).trans_eq (by ring)

end Erdos3

end

end OAI
