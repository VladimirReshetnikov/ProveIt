import OAI.Combinatorics.Progressions.Estimates.AuxiliaryIntervalCells

namespace OAI

section

namespace Erdos3

open scoped BigOperators

abbrev AuxiliaryBoxLabels {I : Type*} {N : I → ℕ}
    (P : ∀ i, FiniteProgressionPartition (N i)) (M d : I → ℕ) (u : I → ℤ) :=
  ∀ i, (P i).Label × CompatibleAuxResidue (M i) (d i) (u i)

noncomputable def boxAuxiliaryCell {I : Type*} (a : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (M d : I → ℕ) (hd : ∀ i, 0 < d i)
    (u r b : I → ℤ)
    (hbase : ∀ i (x : ℤ), x ≡ b i [ZMOD r i] → x ≡ u i [ZMOD (M i : ℤ)])
    (x : IntegerResidueBox a (fun i => a i + N i) r b) : AuxiliaryBoxLabels P M d u :=
  fun i => intervalAuxiliaryCell (a i) (P i) (M i) (d i) (hd i) (u i) (r i) (b i) (hbase i) (x i)

noncomputable def boxAuxiliaryCellEquiv {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i))
    (hstep : ∀ i k, (P i).step k = 1) (hpos : ∀ i k, 0 < (P i).length k)
    (M d : I → ℕ) (hd : ∀ i, 0 < d i) (u r b : I → ℤ)
    (hbase : ∀ i (x : ℤ), x ≡ b i [ZMOD r i] → x ≡ u i [ZMOD (M i : ℤ)])
    (k : AuxiliaryBoxLabels P M d u) (R c : I → ℤ)
    (hcombine : ∀ i (x : ℤ),
      (x ≡ b i [ZMOD r i] ∧ x ≡ ((k i).2.val.val : ℤ) [ZMOD (d i : ℤ)]) ↔ x ≡ c i [ZMOD R i]) :
    ↥(partitionCell (boxAuxiliaryCell a N P M d hd u r b hbase) k) ≃
      IntegerResidueBox (fun i => intervalCellLower (a i) (P i) (k i).1)
        (fun i => intervalCellUpper (a i) (P i) (k i).1) R c := by
  let e₁ : ↥(partitionCell (boxAuxiliaryCell a N P M d hd u r b hbase) k) ≃
      {x : IntegerResidueBox a (fun i => a i + N i) r b //
        ∀ i, intervalAuxiliaryCell (a i) (P i) (M i) (d i) (hd i)
          (u i) (r i) (b i) (hbase i) (x i) = k i} :=
    Equiv.subtypeEquivRight (fun x => by
      simp only [mem_partitionCell, boxAuxiliaryCell, funext_iff])
  exact e₁.trans (Equiv.subtypePiEquivPi.trans (Equiv.piCongrRight (fun i =>
    intervalAuxiliaryCellEquiv (a i) (P i) (hstep i) (hpos i) (M i) (d i) (hd i)
      (u i) (r i) (b i) (hbase i) (k i) (R i) (c i) (hcombine i))))

theorem boxAuxiliaryCell_card {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i))
    (hstep : ∀ i k, (P i).step k = 1) (hpos : ∀ i k, 0 < (P i).length k)
    (M d : I → ℕ) (hd : ∀ i, 0 < d i) (u r b : I → ℤ)
    (hbase : ∀ i (x : ℤ), x ≡ b i [ZMOD r i] → x ≡ u i [ZMOD (M i : ℤ)])
    (k : AuxiliaryBoxLabels P M d u) (R c : I → ℤ)
    (hcombine : ∀ i (x : ℤ),
      (x ≡ b i [ZMOD r i] ∧ x ≡ ((k i).2.val.val : ℤ) [ZMOD (d i : ℤ)]) ↔ x ≡ c i [ZMOD R i]) :
    (partitionCell (boxAuxiliaryCell a N P M d hd u r b hbase) k).card =
      rectangularResidueCount (fun i => intervalCellLower (a i) (P i) (k i).1)
        (fun i => intervalCellUpper (a i) (P i) (k i).1) R c := by
  have he := Fintype.card_congr (boxAuxiliaryCellEquiv a N P hstep hpos M d hd u r b hbase k R c hcombine)
  calc
    _ = Fintype.card (IntegerResidueBox (fun i => intervalCellLower (a i) (P i) (k i).1)
        (fun i => intervalCellUpper (a i) (P i) (k i).1) R c) := by
      simpa only [Fintype.card_coe] using he
    _ = _ := (rectangularResidueCount_eq_card _ _ _ _).symm

theorem boxAuxiliaryCell_mixture {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i))
    (hstep : ∀ i k, (P i).step k = 1) (hpos : ∀ i k, 0 < (P i).length k)
    (M d : I → ℕ) (hd : ∀ i, 0 < d i) (u r b : I → ℤ)
    (hbase : ∀ i (x : ℤ), x ≡ b i [ZMOD r i] → x ≡ u i [ZMOD (M i : ℤ)])
    (R : I → ℤ) (c : AuxiliaryBoxLabels P M d u → I → ℤ)
    (hcombine : ∀ k i (x : ℤ),
      (x ≡ b i [ZMOD r i] ∧ x ≡ ((k i).2.val.val : ℤ) [ZMOD (d i : ℤ)]) ↔ x ≡ c k i [ZMOD R i])
    (f : IntegerResidueBox a (fun i => a i + N i) r b → ℂ) :
    (𝔼 x, f x) = ∑ k : AuxiliaryBoxLabels P M d u,
      ((rectangularResidueCount (fun i => intervalCellLower (a i) (P i) (k i).1)
          (fun i => intervalCellUpper (a i) (P i) (k i).1) R (c k) : ℝ) /
        (∑ j : AuxiliaryBoxLabels P M d u, (rectangularResidueCount
          (fun i => intervalCellLower (a i) (P i) (j i).1)
          (fun i => intervalCellUpper (a i) (P i) (j i).1) R (c j) : ℝ)) : ℂ) *
      (𝔼 x ∈ partitionCell (boxAuxiliaryCell a N P M d hd u r b hbase) k, f x) := by
  have hcard (k : AuxiliaryBoxLabels P M d u) :=
    boxAuxiliaryCell_card a N P hstep hpos M d hd u r b hbase k R (c k) (hcombine k)
  simpa only [hcard] using
    complex_expect_partition_count_weights (boxAuxiliaryCell a N P M d hd u r b hbase) f

end Erdos3

end

end OAI
