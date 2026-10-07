import OAI.Combinatorics.Progressions.Nilpotent.BCHNonlinearRemainder

namespace OAI

section

namespace Erdos3

variable {X : Type*}

def finiteSeriesWeight (s : ℕ) (i : Fin 2 × Fin (s + 1)) : ℚ :=
  if i.1 = 0 then (i.2.val.factorial : ℚ)⁻¹ else (-1 : ℚ) ^ (i.2.val + 1) / i.2.val

def finiteSeriesDenominator (s : ℕ) : ℕ := arrayDenominator (finiteSeriesWeight s)

def finiteSeriesNumerator (s : ℕ) (i : Fin 2 × Fin (s + 1)) : ℤ :=
  clearedArray (finiteSeriesWeight s) i

def finiteSeriesNumeratorBound (s : ℕ) : ℕ :=
  1 + ∑ i, (finiteSeriesNumerator s i).natAbs

theorem finiteSeriesDenominator_pos (s : ℕ) : 0 < finiteSeriesDenominator s :=
  arrayDenominator_pos _

theorem finiteSeriesNumeratorBound_pos (s : ℕ) : 0 < finiteSeriesNumeratorBound s := by
  unfold finiteSeriesNumeratorBound
  omega

theorem finiteSeriesNumerator_cast (s : ℕ) (i : Fin 2 × Fin (s + 1)) :
    (finiteSeriesNumerator s i : ℚ) = (finiteSeriesDenominator s : ℚ) * finiteSeriesWeight s i :=
  clearedArray_cast _ _

theorem finiteSeriesNumerator_le (s : ℕ) (i : Fin 2 × Fin (s + 1)) :
    (finiteSeriesNumerator s i).natAbs ≤ finiteSeriesNumeratorBound s := by
  have h := Finset.single_le_sum (f := fun j => (finiteSeriesNumerator s j).natAbs)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  exact h.trans (Nat.le_add_left _ 1)

theorem finiteExp_freeCoefficientBound (s : ℕ) (x : X) :
    FreeCoefficientBound s (finiteSeriesDenominator s)
      ((s + 1) * finiteSeriesNumeratorBound s) (finiteExp (s + 1) (FreeAlgebra.ι ℚ x)) := by
  have hterm : ∀ i ∈ Finset.range (s + 1),
      FreeCoefficientBound s (finiteSeriesDenominator s) (finiteSeriesNumeratorBound s)
        ((i.factorial : ℚ)⁻¹ • (FreeAlgebra.ι ℚ x) ^ i) := by
    intro i hi
    let j : Fin 2 × Fin (s + 1) := (0, ⟨i, Finset.mem_range.mp hi⟩)
    have h := (FreeCoefficientBound.word s ((FreeMonoid.of x) ^ i)).smul
      (finiteSeriesNumerator_cast s j) (finiteSeriesNumerator_le s j)
    simpa only [j, finiteSeriesWeight, ite_true, mul_one, map_pow, freeWord_of] using h
  simpa only [finiteExp, Finset.card_range] using
    FreeCoefficientBound.sum_finset (Finset.range (s + 1)) _ hterm

theorem finiteLog_freeCoefficientBound {s D M : ℕ} {p : FreeAlgebra ℚ X}
    (hp : FreeCoefficientBound s D M p) :
    FreeCoefficientBound s (finiteSeriesDenominator s * D ^ s)
      ((s + 1) * finiteSeriesNumeratorBound s * (D + (s + 1) * M) ^ s) (finiteLog (s + 1) p) := by
  have hterm : ∀ i ∈ Finset.range (s + 1),
      FreeCoefficientBound s (finiteSeriesDenominator s * D ^ s)
        (finiteSeriesNumeratorBound s * (D + (s + 1) * M) ^ s)
        (((-1 : ℚ) ^ (i + 1) / i) • p ^ i) := by
    intro i hi
    have his : i ≤ s := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    let j : Fin 2 × Fin (s + 1) := (1, ⟨i, Finset.mem_range.mp hi⟩)
    have h := ((hp.pow i).smul (finiteSeriesNumerator_cast s j)
      (finiteSeriesNumerator_le s j)).enlarge_denominator (D ^ (s - i))
    have hden : D ^ (s - i) * (finiteSeriesDenominator s * D ^ i) = finiteSeriesDenominator s * D ^ s := by
      rw [mul_left_comm, ← pow_add, Nat.sub_add_cancel his]
    rw [hden] at h
    have hmass : D ^ (s - i) * (finiteSeriesNumeratorBound s * (((s + 1) * M) ^ i)) ≤
        finiteSeriesNumeratorBound s * (D + (s + 1) * M) ^ s := by
      calc
        _ = finiteSeriesNumeratorBound s * (D ^ (s - i) * (((s + 1) * M) ^ i)) := by ring
        _ ≤ finiteSeriesNumeratorBound s *
            ((D + (s + 1) * M) ^ (s - i) * (D + (s + 1) * M) ^ i) := by
          apply Nat.mul_le_mul_left
          exact Nat.mul_le_mul (Nat.pow_le_pow_left (Nat.le_add_right _ _) _)
            (Nat.pow_le_pow_left (Nat.le_add_left _ _) _)
        _ = _ := by rw [← pow_add, Nat.sub_add_cancel his]
    simpa only [j, finiteSeriesWeight, show (1 : Fin 2) ≠ 0 from by decide, ite_false] using h.mono hmass
  simpa only [finiteLog, Finset.card_range, mul_assoc] using
    FreeCoefficientBound.sum_finset (Finset.range (s + 1)) _ hterm

def bchProductDenominator (s n : ℕ) : ℕ :=
  finiteSeriesDenominator s * (finiteSeriesDenominator s ^ n) ^ s

def bchProductNumeratorBound (s n : ℕ) : ℕ :=
  (s + 1) * finiteSeriesNumeratorBound s *
    (finiteSeriesDenominator s ^ n + (s + 1) *
      ((((s + 1) * ((s + 1) * finiteSeriesNumeratorBound s)) ^ n) + finiteSeriesDenominator s ^ n)) ^ s

theorem bchProductDenominator_pos (s n : ℕ) : 0 < bchProductDenominator s n := by
  unfold bchProductDenominator
  exact Nat.mul_pos (finiteSeriesDenominator_pos s) (pow_pos (pow_pos (finiteSeriesDenominator_pos s) _) _)

theorem bchProductPolynomial_coefficient_bound (s : ℕ) (xs : List X) :
    FreeCoefficientBound s (bchProductDenominator s xs.length) (bchProductNumeratorBound s xs.length)
      (bchProductPolynomial s xs) := by
  have hprod := FreeCoefficientBound.list_prod
    (xs.map (fun x => finiteExp (s + 1) (FreeAlgebra.ι ℚ x))) (by
      intro p hp
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp hp
      exact finiteExp_freeCoefficientBound s x)
  simp only [List.length_map] at hprod
  have hone := (FreeCoefficientBound.one (X := X) s).enlarge_denominator
    (finiteSeriesDenominator s ^ xs.length)
  simp only [mul_one] at hone
  have hsub := hprod.add_same hone.neg
  rw [← sub_eq_add_neg] at hsub
  exact finiteLog_freeCoefficientBound hsub

end Erdos3

end

end OAI
