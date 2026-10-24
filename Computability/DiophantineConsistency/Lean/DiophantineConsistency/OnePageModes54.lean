import DiophantineConsistency.OnePageModesData54

namespace DiophantineConsistency.OnePageModes54

open NativeClauseModes54 NativeModesData54
open scoped BigOperators

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

attribute [local irreducible] tailMode tailPermutation key NativeModesData54.mode

/-- At nonnegative arguments below Q, the page quotient is a strict-order
indicator, including the diagonal case. -/
theorem quotient_indicator {a b : ℕ} (ha : a<Q) (hb : b<Q) :
    (Q+a-b-1)/Q = if b < a then 1 else 0 := by
  unfold Q at *
  split_ifs <;> omega

/-- The signed floor in the page has exactly the same order-indicator value.
The key bounds also ensure that its numerator is nonnegative. -/
theorem integer_quotient_indicator {a b : ℕ} (ha : a < Q) (hb : b < Q) :
    ((Q : ℤ) + a - b - 1) / (Q : ℤ) = if b < a then 1 else 0 := by
  unfold Q at *
  split_ifs <;> omega

theorem quotient_cast {a b : ℕ} (ha : a < Q) (hb : b < Q) :
    (((Q+a-b-1)/Q : ℕ) : ℤ) = ((Q : ℤ)+a-b-1)/(Q : ℤ) := by
  rw [quotient_indicator ha hb,integer_quotient_indicator ha hb]
  split_ifs <;> rfl

private theorem count_before {n : ℕ} (i : Fin n) :
    (∑j : Fin n, if j < i then 1 else 0 : ℕ) = i.val := by
  have hf : (Finset.univ.filter fun j : Fin n => j < i) = Finset.Iio i := by
    ext j
    simp
  rw [Finset.sum_boole,hf,Fin.card_Iio]
  rfl

/-- The tail rank is given by the exact fixed quotient sum printed on the
page; the finite permutation is absent from this definition. -/
def tailRank (i : Fin 455) : ℕ :=
  2 + ∑j : Fin 455, (Q+key (tailMode i).1-key (tailMode j).1-1)/Q

theorem tailRank_eq (i : Fin 455) : tailRank i = 2+(tailPermutation i).val := by
  unfold tailRank
  apply congrArg (fun n : ℕ => 2 + n)
  calc
    (∑j : Fin 455, (Q+key (tailMode i).1-key (tailMode j).1-1)/Q) =
        ∑j : Fin 455, if tailPermutation j < tailPermutation i then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [quotient_indicator (tail_key_lt i) (tail_key_lt j),tailMode_eq i,tailMode_eq j]
      simp only [sorted_strict.lt_iff_lt]
    _ = ∑j : Fin 455, if j < tailPermutation i then 1 else 0 :=
      Equiv.sum_comp tailPermutation (fun j=>if j < tailPermutation i then 1 else 0)
    _ = (tailPermutation i).val := count_before _

def arithmeticRank (i : Fin 457) : ℕ := Fin.addCases (m := 2) (n := 455) (fun j => j.val) tailRank i

noncomputable def permutation : Equiv.Perm (Fin 457) :=
  finSumFinEquiv.symm.trans (((Equiv.refl (Fin 2)).sumCongr tailPermutation).trans finSumFinEquiv)

@[simp] theorem permutation_prefix (i : Fin 2) :
    permutation (Fin.castAdd 455 i) = Fin.castAdd 455 i := by
  change finSumFinEquiv (Sum.map id (fun j => tailPermutation j)
    ((finSumFinEquiv (m := 2) (n := 455)).symm (Fin.castAdd 455 i))) = _
  rw [finSumFinEquiv_symm_apply_castAdd (n := 455) i]
  rfl

@[simp] theorem permutation_tail (i : Fin 455) :
    permutation (Fin.natAdd 2 i) = Fin.natAdd 2 (tailPermutation i) := by
  change finSumFinEquiv (Sum.map id (fun j => tailPermutation j)
    ((finSumFinEquiv (m := 2) (n := 455)).symm (Fin.natAdd 2 i))) = _
  rw [finSumFinEquiv_symm_apply_natAdd (m := 2) i]
  rfl

theorem arithmeticRank_eq (i : Fin 457) : arithmeticRank i = (permutation i).val := by
  refine Fin.addCases (m := 2) (n := 455) ?_ ?_ i
  · intro j
    rw [permutation_prefix]
    change Fin.addCases (m := 2) (n := 455) (fun k => k.val) tailRank
      (Fin.castAdd 455 j) = j.val
    rw [Fin.addCases_left]
  · intro j
    rw [permutation_tail]
    change Fin.addCases (m := 2) (n := 455) (fun k => k.val) tailRank
      (Fin.natAdd 2 j) = 2 + (tailPermutation j).val
    rw [Fin.addCases_right]
    exact tailRank_eq j

theorem arithmeticRank_lt (i : Fin 457) : arithmeticRank i<457 := by
  rw [arithmeticRank_eq]
  exact (permutation i).isLt

theorem unsortedMode_eq (i : Fin 457) : unsortedMode i = mode (permutation i) := by
  refine Fin.addCases (m := 2) (n := 455) ?_ ?_ i
  · intro j
    rw [permutation_prefix]
    fin_cases j
    · change (⟨2,3,3,1⟩,.ordinary) = mode 0
      exact mode_zero.symm
    · change (⟨5,0,0,0⟩,.ordinary) = mode 1
      exact mode_one.symm
  · intro j
    rw [permutation_tail]
    rw [unsortedMode,Fin.addCases_right]
    exact tailMode_eq j

theorem mode_at_arithmeticRank (i : Fin 457) :
    mode ⟨arithmeticRank i,arithmeticRank_lt i⟩=unsortedMode i := by
  rw [unsortedMode_eq]
  congr 1
  exact Fin.ext (arithmeticRank_eq i)

end DiophantineConsistency.OnePageModes54
