import OAI.Combinatorics.Progressions.Lattices.PhysicalSubboxResidueSlice

namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def comparableBoxPartitions {I : Type*} (N H : I → ℕ)
    (hH : ∀ i, 0 < H i) (hHN : ∀ i, H i ≤ N i) : ∀ i, FiniteProgressionPartition (N i) :=
  fun i => FiniteProgressionPartition.mergedIntervals (N i) (H i) (hH i) (hHN i)

theorem comparableBoxPartitions_step {I : Type*} (N H : I → ℕ)
    (hH : ∀ i, 0 < H i) (hHN : ∀ i, H i ≤ N i) (i : I)
    (k : (comparableBoxPartitions N H hH hHN i).Label) :
    (comparableBoxPartitions N H hH hHN i).step k = 1 := rfl

theorem comparableBoxPartitions_length {I : Type*} (N H : I → ℕ)
    (hH : ∀ i, 0 < H i) (hHN : ∀ i, H i ≤ N i) (i : I)
    (k : (comparableBoxPartitions N H hH hHN i).Label) :
    H i ≤ (comparableBoxPartitions N H hH hHN i).length k ∧
      (comparableBoxPartitions N H hH hHN i).length k < 2 * H i :=
  FiniteProgressionPartition.mergedIntervals_length_bounds (N i) (H i) (hH i) (hHN i) k

theorem comparableBoxPartitions_nonempty {I : Type*} (N H : I → ℕ)
    (hH : ∀ i, 0 < H i) (hHN : ∀ i, H i ≤ N i) :
    Nonempty (∀ i, (comparableBoxPartitions N H hH hHN i).Label) :=
  ⟨fun i => ⟨0, Nat.div_pos (hHN i) (hH i)⟩⟩

theorem comparableBoxPartitions_card {I : Type*} [Fintype I] [DecidableEq I]
    (N H : I → ℕ) (hH : ∀ i, 0 < H i) (hHN : ∀ i, H i ≤ N i) :
    Fintype.card (∀ i, (comparableBoxPartitions N H hH hHN i).Label) = ∏ i, N i / H i := by
  rw [Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro i _
  exact FiniteProgressionPartition.mergedIntervals_card (N i) (H i) (hH i) (hHN i)

theorem intervalCell_width (a : ℤ) {N : ℕ} (P : FiniteProgressionPartition N) (k : P.Label) :
    intervalCellUpper a P k - intervalCellLower a P k = P.length k := by
  dsimp only [intervalCellLower, intervalCellUpper]
  omega

theorem comparableBoxPartitions_ratio_le {I : Type*} [Fintype I]
    (a : I → ℤ) (N H : I → ℕ) (hH : ∀ i, 0 < H i) (hHN : ∀ i, H i ≤ N i)
    (r : I → ℤ) (hr : ∀ i, 0 ≤ r i)
    (k : ∀ i, (comparableBoxPartitions N H hH hHN i).Label) :
    (∑ i, (r i : ℝ) /
      ((intervalCellUpper (a i) (comparableBoxPartitions N H hH hHN i) (k i) -
        intervalCellLower (a i) (comparableBoxPartitions N H hH hHN i) (k i) : ℤ) : ℝ)) ≤
      ∑ i, (r i : ℝ) / (H i : ℝ) := by
  apply Finset.sum_le_sum
  intro i _
  rw [intervalCell_width]
  have hlen : (H i : ℝ) ≤ (comparableBoxPartitions N H hH hHN i).length (k i) := by
    exact_mod_cast (comparableBoxPartitions_length N H hH hHN i (k i)).1
  simp only [Int.cast_natCast]
  exact div_le_div_of_nonneg_left (by exact_mod_cast hr i) (by exact_mod_cast hH i) hlen

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem translatedIntegerBox_eq_piFinset (lo : I → ℤ) (N : I → ℕ) :
    translatedIntegerBox lo N = Fintype.piFinset (fun i => Finset.Ico (lo i) (lo i + N i)) := by
  ext x
  simp only [mem_translatedIntegerBox, Fintype.mem_piFinset, Finset.mem_Ico]

noncomputable def physicalBoxUnitResidueEquiv (lo : I → ℤ) (N : I → ℕ) :
    translatedIntegerBox lo N ≃ IntegerResidueBox lo (fun i => lo i + N i) (fun _ => 1) (fun _ => 0) where
  toFun x i := ⟨x.val i, Finset.mem_filter.mpr
    ⟨Finset.mem_Ico.mpr ((mem_translatedIntegerBox lo N x.val).mp x.property i), Int.modEq_one⟩⟩
  invFun x := ⟨fun i => (x i).val, (mem_translatedIntegerBox lo N _).mpr
    (fun i => Finset.mem_Ico.mp (Finset.mem_filter.mp (x i).property).1)⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def physicalBoxCell (lo : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (x : translatedIntegerBox lo N) : ∀ i, (P i).Label :=
  boxIntervalResidueCell lo N P (fun _ => 1) (fun _ => 0) (physicalBoxUnitResidueEquiv lo N x)

theorem physicalBoxCell_eq_iff (lo : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (hstep : ∀ i c, (P i).step c = 1)
    (x : translatedIntegerBox lo N) (c : ∀ i, (P i).Label) :
    physicalBoxCell lo N P x = c ↔ ∀ i,
      intervalCellLower (lo i) (P i) (c i) ≤ x.val i ∧ x.val i < intervalCellUpper (lo i) (P i) (c i) := by
  change (fun i => intervalResidueCell (lo i) (P i) 1 0 ((physicalBoxUnitResidueEquiv lo N x) i)) = c ↔ _
  rw [funext_iff]
  exact forall_congr' (fun i => intervalResidueCell_eq_iff (lo i) (P i) (hstep i) 1 0 _ (c i))

noncomputable def physicalBoxCellEquiv (lo : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (hstep : ∀ i c, (P i).step c = 1)
    (hpos : ∀ i c, 0 < (P i).length c) (c : ∀ i, (P i).Label) :
    {x : translatedIntegerBox lo N // physicalBoxCell lo N P x = c} ≃
      IntegerResidueBox (fun i => intervalCellLower (lo i) (P i) (c i))
        (fun i => intervalCellLower (lo i) (P i) (c i) + (P i).length (c i))
        (fun _ => 1) (fun _ => 0) := by
  let e : {x : translatedIntegerBox lo N // physicalBoxCell lo N P x = c} ≃
      ↥(partitionCell (boxIntervalResidueCell lo N P (fun _ => 1) (fun _ => 0)) c) :=
    (physicalBoxUnitResidueEquiv lo N).subtypeEquiv (fun x =>
      (mem_partitionCell (boxIntervalResidueCell lo N P (fun _ => 1) (fun _ => 0)) c
        (physicalBoxUnitResidueEquiv lo N x)).symm)
  exact e.trans (boxIntervalResidueCellEquiv lo N P hstep hpos (fun _ => 1) (fun _ => 0) c)

theorem physicalBoxCellEquiv_val (lo : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (hstep : ∀ i c, (P i).step c = 1)
    (hpos : ∀ i c, 0 < (P i).length c) (c : ∀ i, (P i).Label)
    (x : {x : translatedIntegerBox lo N // physicalBoxCell lo N P x = c}) (i : I) :
    (physicalBoxCellEquiv lo N P hstep hpos c x i).val = x.val.val i := rfl

omit [Fintype I] [DecidableEq I] in
theorem physicalBoxCell_nonempty (lo : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (hpos : ∀ i c, 0 < (P i).length c)
    (c : ∀ i, (P i).Label) :
    Nonempty (IntegerResidueBox (fun i => intervalCellLower (lo i) (P i) (c i))
      (fun i => intervalCellLower (lo i) (P i) (c i) + (P i).length (c i))
      (fun _ => 1) (fun _ => 0)) := by
  refine ⟨fun i => ⟨intervalCellLower (lo i) (P i) (c i), Finset.mem_filter.mpr ⟨?_, Int.modEq_one⟩⟩⟩
  exact Finset.mem_Ico.mpr ⟨le_rfl, lt_add_of_pos_right _ (by exact_mod_cast hpos i (c i))⟩

theorem physicalBoxCell_subset (lo : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (hstep : ∀ i c, (P i).step c = 1)
    (hpos : ∀ i c, 0 < (P i).length c) (c : ∀ i, (P i).Label) :
    translatedIntegerBox (fun i => intervalCellLower (lo i) (P i) (c i)) (fun i => (P i).length (c i)) ⊆
      translatedIntegerBox lo N := by
  intro x hx
  apply (mem_translatedIntegerBox lo N x).mpr
  intro i
  have hi := (mem_translatedIntegerBox _ _ x).mp hx i
  have hend : ((P i).start (c i) : ℤ) + (P i).length (c i) ≤ N i := by
    exact_mod_cast (P i).end_le_of_step_one (hstep i) (c i) (hpos i (c i))
  have hstart : (0 : ℤ) ≤ (P i).start (c i) := Int.natCast_nonneg _
  dsimp only [intervalCellLower] at hi
  constructor <;> omega

theorem physicalBoxCell_distance_lower (lo : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (hstep : ∀ i c, (P i).step c = 1)
    (x : translatedIntegerBox lo N) (i : I) :
    |(x.val i : ℝ) - (intervalCellLower (lo i) (P i) (physicalBoxCell lo N P x i) : ℝ)| ≤
      ((P i).length (physicalBoxCell lo N P x i) : ℝ) := by
  have hi := (physicalBoxCell_eq_iff lo N P hstep x _).mp rfl i
  have hlo : (intervalCellLower (lo i) (P i) (physicalBoxCell lo N P x i) : ℝ) ≤ x.val i := by
    exact_mod_cast hi.1
  have hhi : (x.val i : ℝ) < (intervalCellLower (lo i) (P i) (physicalBoxCell lo N P x i) : ℝ) +
      ((P i).length (physicalBoxCell lo N P x i) : ℝ) := by exact_mod_cast hi.2
  rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
  linarith

end Erdos3

end

end OAI
