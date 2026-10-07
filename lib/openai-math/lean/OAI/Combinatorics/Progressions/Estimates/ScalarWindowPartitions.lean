import Mathlib.Algebra.Order.Floor.Ring
import OAI.Combinatorics.Progressions.Geometry.PhysicalBoxPartition

namespace OAI

section

namespace Erdos3

noncomputable def scalarWindowLength (N : ℕ) (S : ℝ) : ℕ :=
  min N ⌊S / 4⌋₊

theorem scalarWindowLength_bounds {N : ℕ} {S K : ℝ}
    (hN : 0 < N) (hS : 4 ≤ S) (hK : 0 ≤ K) (hratio : S ≤ K * N) :
    0 < scalarWindowLength N S ∧ scalarWindowLength N S ≤ N ∧
      2 * (scalarWindowLength N S : ℝ) ≤ S / 2 ∧
      S ≤ (K + 8) * scalarWindowLength N S := by
  have hfloor : 1 ≤ ⌊S / 4⌋₊ := (Nat.le_floor_iff (by positivity : 0 ≤ S / 4)).mpr (by norm_num; linarith)
  have hfloorle : (⌊S / 4⌋₊ : ℝ) ≤ S / 4 := Nat.floor_le (by positivity)
  have hgap : S / 4 < (⌊S / 4⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one (S / 4)
  have hpositive : 0 < scalarWindowLength N S := lt_min hN (by omega)
  have hsmall : scalarWindowLength N S ≤ ⌊S / 4⌋₊ := min_le_right _ _
  have hsmallreal : (scalarWindowLength N S : ℝ) ≤ (⌊S / 4⌋₊ : ℝ) := by exact_mod_cast hsmall
  refine ⟨hpositive, min_le_left _ _, by linarith, ?_⟩
  by_cases hNF : N ≤ ⌊S / 4⌋₊
  · rw [scalarWindowLength, min_eq_left hNF]
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  · rw [scalarWindowLength, min_eq_right (le_of_not_ge hNF)]
    have hfloorreal : (1 : ℝ) ≤ ⌊S / 4⌋₊ := by exact_mod_cast hfloor
    nlinarith [mul_nonneg hK (Nat.cast_nonneg (α := ℝ) ⌊S / 4⌋₊)]

theorem exists_scalarWindowPartitions {I : Type*} (N : I → ℕ) (S : I → ℝ) (K : ℝ)
    (hN : ∀ i, 0 < N i) (hS : ∀ i, 4 ≤ S i) (hK : 0 ≤ K)
    (hratio : ∀ i, S i ≤ K * N i) :
    ∃ P : ∀ i, FiniteProgressionPartition (N i),
      (∀ i c, (P i).step c = 1) ∧ (∀ i c, 0 < (P i).length c) ∧
      (∀ i c, ((P i).length c : ℝ) ≤ S i / 2) ∧
      (∀ i c, S i ≤ (K + 8) * (P i).length c) := by
  let H := fun i => scalarWindowLength (N i) (S i)
  have hbounds i := scalarWindowLength_bounds (hN i) (hS i) hK (hratio i)
  let P := comparableBoxPartitions N H (fun i => (hbounds i).1) (fun i => (hbounds i).2.1)
  have hlength i c := comparableBoxPartitions_length N H (fun i => (hbounds i).1)
    (fun i => (hbounds i).2.1) i c
  refine ⟨P, comparableBoxPartitions_step _ _ _ _, ?_, ?_, ?_⟩
  · intro i c
    exact (hbounds i).1.trans_le (hlength i c).1
  · intro i c
    have hlen : ((P i).length c : ℝ) < 2 * H i := by exact_mod_cast (hlength i c).2
    exact hlen.le.trans (hbounds i).2.2.1
  · intro i c
    exact (hbounds i).2.2.2.trans (mul_le_mul_of_nonneg_left
      (by exact_mod_cast (hlength i c).1) (by linarith))

end Erdos3

end

end OAI
