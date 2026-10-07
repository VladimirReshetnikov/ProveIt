import OAI.Combinatorics.Progressions.Geometry.PhysicalBoxPartition
import OAI.Combinatorics.Progressions.Lattices.CommonStrideResidueGeometry
import OAI.Combinatorics.Progressions.Probability.AuxiliaryBoxLaws

namespace OAI

section

namespace Erdos3

theorem mem_boxAuxiliaryCell_iff {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i))
    (hstep : ∀ i k, (P i).step k = 1)
    (M d : I → ℕ) (hd : ∀ i, 0 < d i) (u r b : I → ℤ)
    (hbase : ∀ i (x : ℤ), x ≡ b i [ZMOD r i] → x ≡ u i [ZMOD (M i : ℤ)])
    (k : AuxiliaryBoxLabels P M d u) (x : IntegerResidueBox a (fun i => a i + N i) r b) :
    x ∈ partitionCell (boxAuxiliaryCell a N P M d hd u r b hbase) k ↔
      ∀ i, (intervalCellLower (a i) (P i) (k i).1 ≤ (x i).val ∧
        (x i).val < intervalCellUpper (a i) (P i) (k i).1) ∧
        (x i).val ≡ ((k i).2.val.val : ℤ) [ZMOD (d i : ℤ)] := by
  simp only [mem_partitionCell, boxAuxiliaryCell, funext_iff]
  apply forall_congr'
  intro i
  exact intervalAuxiliaryCell_eq_iff (a i) (P i) (hstep i) (M i) (d i) (hd i)
    (u i) (r i) (b i) (hbase i) (x i) (k i)

theorem boxAuxiliaryCell_same_piece {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i))
    (hstep : ∀ i k, (P i).step k = 1)
    (M d : I → ℕ) (hd : ∀ i, 0 < d i) (u r b s c : I → ℤ)
    (hbaseR : ∀ i (x : ℤ), x ≡ b i [ZMOD r i] → x ≡ u i [ZMOD (M i : ℤ)])
    (hbaseS : ∀ i (x : ℤ), x ≡ c i [ZMOD s i] → x ≡ u i [ZMOD (M i : ℤ)])
    (k : AuxiliaryBoxLabels P M d u)
    (x : IntegerResidueBox a (fun i => a i + N i) r b)
    (y : IntegerResidueBox a (fun i => a i + N i) s c)
    (hx : x ∈ partitionCell (boxAuxiliaryCell a N P M d hd u r b hbaseR) k)
    (hy : y ∈ partitionCell (boxAuxiliaryCell a N P M d hd u s c hbaseS) k) :
    ∀ i, (d i : ℤ) ∣ (x i).val - (y i).val ∧
      |((x i).val : ℝ) - ((y i).val : ℝ)| < ((P i).length (k i).1 : ℝ) := by
  have hx' := (mem_boxAuxiliaryCell_iff a N P hstep M d hd u r b hbaseR k x).mp hx
  have hy' := (mem_boxAuxiliaryCell_iff a N P hstep M d hd u s c hbaseS k y).mp hy
  intro i
  refine ⟨Int.modEq_iff_dvd.mp ((hy' i).2.trans (hx' i).2.symm), ?_⟩
  have hxi := (hx' i).1
  have hyi := (hy' i).1
  have hw := intervalCell_width (a i) (P i) (k i).1
  have hdiff : |(x i).val - (y i).val| < ((P i).length (k i).1 : ℤ) :=
    abs_lt.mpr ⟨by omega, by omega⟩
  exact_mod_cast hdiff

end Erdos3

end

section

namespace Erdos3

theorem commonStrideIndex_bound {I : Type*} (c : I → ℤ) {m : ℕ} (hm : 0 < m)
    (y : I → ℤ) (hy : ∀ i, y i ≡ c i [ZMOD (m : ℤ)]) (A : I → ℝ)
    (hbound : ∀ i, |(y i : ℝ) - (c i : ℝ)| ≤ (m : ℝ) * A i) :
    ∀ i, |(commonStrideIndex c m y i : ℝ)| ≤ A i := by
  have h := commonStrideIndex_distance_le c hm y c hy (fun i => Int.ModEq.refl (c i)) A 1
    (by simpa only [mul_one] using hbound)
  simpa only [commonStrideIndex, sub_self, Int.zero_ediv, Int.cast_zero, sub_zero, mul_one] using h

theorem auxiliaryPiece_stride_geometry {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℤ) (N : I → ℕ) (Q : ∀ i, FiniteProgressionPartition (N i))
    (hstep : ∀ i k, (Q i).step k = 1) (M q : ℕ) (hM : 0 < M) (hq : 0 < q)
    (u r b : I → ℤ) (hbase : ∀ i (x : ℤ), x ≡ b i [ZMOD r i] → x ≡ u i [ZMOD (M : ℤ)])
    (k : AuxiliaryBoxLabels Q (fun _ => M) (fun _ => M * q) u)
    (y : IntegerResidueBox a (fun i => a i + N i) r b)
    (z : IntegerResidueBox a (fun i => a i + N i) (fun _ => (M : ℤ)) u)
    (hy : y ∈ partitionCell (boxAuxiliaryCell a N Q (fun _ => M) (fun _ => M * q)
      (fun _ => Nat.mul_pos hM hq) u r b hbase) k)
    (hz : z ∈ partitionCell (baseAuxiliaryBoxCell a N Q (fun _ => M) (fun _ => M * q)
      (fun _ => Nat.mul_pos hM hq) u) k)
    (A : I → ℝ) (δ : ℝ)
    (hwidth : ∀ i, ((Q i).length (k i).1 : ℝ) ≤ (M : ℝ) * A i * δ) :
    (∀ i, (q : ℤ) ∣ commonStrideIndex u M (fun j => (y j).val) i -
      commonStrideIndex u M (fun j => (z j).val) i) ∧
    (∀ i, |(commonStrideIndex u M (fun j => (y j).val) i : ℝ) -
      (commonStrideIndex u M (fun j => (z j).val) i : ℝ)| ≤ A i * δ) := by
  have hgeom := boxAuxiliaryCell_same_piece a N Q hstep (fun _ => M) (fun _ => M * q)
    (fun _ => Nat.mul_pos hM hq) u r b (fun _ => (M : ℤ)) u hbase (fun _ _ hx => hx) k y z hy hz
  have hmy : ∀ i, (y i).val ≡ u i [ZMOD (M : ℤ)] :=
    fun i => hbase i (y i).val (Finset.mem_filter.mp (y i).property).2
  have hmz : ∀ i, (z i).val ≡ u i [ZMOD (M : ℤ)] :=
    fun i => (Finset.mem_filter.mp (z i).property).2
  exact ⟨commonStrideIndex_period u hM q _ _ hmy hmz (fun i => (hgeom i).1),
    commonStrideIndex_distance_le u hM _ _ hmy hmz A δ (fun i => (hgeom i).2.le.trans (hwidth i))⟩

end Erdos3

end

end OAI
