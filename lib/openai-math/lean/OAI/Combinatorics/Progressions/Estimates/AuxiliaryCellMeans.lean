import OAI.Combinatorics.Progressions.Probability.AuxiliaryBoxLaws

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem boxAuxiliaryCell_expect {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i))
    (hstep : ∀ i k, (P i).step k = 1) (hpos : ∀ i k, 0 < (P i).length k)
    (M d : I → ℕ) (hd : ∀ i, 0 < d i) (u r b : I → ℤ)
    (hbase : ∀ i (x : ℤ), x ≡ b i [ZMOD r i] → x ≡ u i [ZMOD (M i : ℤ)])
    (k : AuxiliaryBoxLabels P M d u) (R c : I → ℤ)
    (hcombine : ∀ i (x : ℤ),
      (x ≡ b i [ZMOD r i] ∧ x ≡ ((k i).2.val.val : ℤ) [ZMOD (d i : ℤ)]) ↔ x ≡ c i [ZMOD R i])
    (f : (I → ℤ) → ℂ) :
    (𝔼 x ∈ partitionCell (boxAuxiliaryCell a N P M d hd u r b hbase) k,
      f (fun i => (x i).val)) =
      𝔼 x : IntegerResidueBox (fun i => intervalCellLower (a i) (P i) (k i).1)
        (fun i => intervalCellUpper (a i) (P i) (k i).1) R c,
        f (fun i => (x i).val) := by
  let B := partitionCell (boxAuxiliaryCell a N P M d hd u r b hbase) k
  let g : IntegerResidueBox a (fun i => a i + N i) r b → ℂ := fun x => f (fun i => (x i).val)
  have he := Fintype.expect_equiv (boxAuxiliaryCellEquiv a N P hstep hpos M d hd u r b hbase k R c hcombine)
    (fun x => g x.val) (fun x => f (fun i => (x i).val)) (fun _ => rfl)
  have hcoe : (𝔼 x : ↥B, g x.val) = 𝔼 x ∈ B, g x := by
    rw [Fintype.expect_eq_sum_div_card, Finset.expect_eq_sum_div_card,
      Fintype.card_coe, Finset.sum_coe_sort]
  exact hcoe.symm.trans he

theorem baseAuxiliaryBoxCell_expect {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i))
    (hstep : ∀ i k, (P i).step k = 1) (hpos : ∀ i k, 0 < (P i).length k)
    (M d : I → ℕ) (hd : ∀ i, 0 < d i) (u : I → ℤ)
    (k : AuxiliaryBoxLabels P M d u) (f : (I → ℤ) → ℂ) :
    (𝔼 x ∈ partitionCell (baseAuxiliaryBoxCell a N P M d hd u) k,
      f (fun i => (x i).val)) =
      𝔼 x : IntegerResidueBox (fun i => intervalCellLower (a i) (P i) (k i).1)
        (fun i => intervalCellUpper (a i) (P i) (k i).1)
        (fun i => (Nat.lcm (M i) (d i) : ℤ)) (fun i => (k i).2.baseValue),
        f (fun i => (x i).val) :=
  boxAuxiliaryCell_expect a N P hstep hpos M d hd u (fun i => (M i : ℤ)) u
    (fun _ _ hx => hx) k (fun i => (Nat.lcm (M i) (d i) : ℤ)) (fun i => (k i).2.baseValue)
    (fun i => (k i).2.baseConstraint_iff) f

theorem refinedAuxiliaryBoxCell_expect {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i))
    (hstep : ∀ i k, (P i).step k = 1) (hpos : ∀ i k, 0 < (P i).length k)
    (M d J : I → ℕ) (hd : ∀ i, 0 < d i) (u w : I → ℤ)
    (hw : ∀ i, w i ≡ u i [ZMOD (M i : ℤ)]) (hcop : ∀ i, (M i * d i).Coprime (J i))
    (k : AuxiliaryBoxLabels P M d u) (f : (I → ℤ) → ℂ) :
    (𝔼 x ∈ partitionCell (refinedAuxiliaryBoxCell a N P M d J hd u w hw) k,
      f (fun i => (x i).val)) =
      𝔼 x : IntegerResidueBox (fun i => intervalCellLower (a i) (P i) (k i).1)
        (fun i => intervalCellUpper (a i) (P i) (k i).1)
        (fun i => (Nat.lcm (M i) (d i) * J i : ℕ))
        (fun i => (k i).2.refinedValue (hcop i) (w i)),
        f (fun i => (x i).val) :=
  boxAuxiliaryCell_expect a N P hstep hpos M d hd u (fun i => (M i * J i : ℕ)) w
    (fun i => refinedResidue_implies_base (M i) (J i) (u i) (w i) (hw i)) k
    (fun i => (Nat.lcm (M i) (d i) * J i : ℕ)) (fun i => (k i).2.refinedValue (hcop i) (w i))
    (fun i => (k i).2.refinedConstraint_iff (hcop i) (w i) (hw i)) f

end Erdos3

end

end OAI
