import DiophantineConsistency.CurrentPolynomialWindow2011

namespace DiophantineConsistency.CurrentPolynomialWindow2011Checks

open CurrentPolynomialWindow2011 CurrentKernel2011 CurrentWindowCarry2011

example : polynomial = CurrentCarrierArithmetic2011.polynomial65 (K : ℤ) := rfl

-- The endpoint has just the actual positive polynomial zero as its premise.
example (v : Fin 14 → ℤ) (hv : ∀ j, 0 < v j)
    (hz : MvPolynomial.eval v (Carrier65.polynomial ports) = 0) :
    ∃ N, ∃ hN : 0 < N, Window v N hN :=
  polynomial_zero_window v hv hz

-- Nat coordinates agree with the original positive integer J, F and w.
example {N : ℕ} [NeZero (N * 2011)] (v : Fin 14 → ℤ) (hv : ∀ j, 0 < v j)
    (x : Fin 31 → ℕ) (c k digits : ZMod (N * 2011) → ℕ) (h : Facts v N x c k digits) :
    (x 0 : ℤ) = v 0 ∧ (x 1 : ℤ) = v 1 ∧ (x 10 : ℤ) = v 8 := by
  rw [h.source_J, h.source_F, h.source_w,
    Int.toNat_of_nonneg (hv 0).le, Int.toNat_of_nonneg (hv 1).le,
    Int.toNat_of_nonneg (hv 8).le]
  exact ⟨rfl, rfl, rfl⟩

-- The actual repeated high mask has origin3, not the unborrowed cell digit4.
example {N : ℕ} [NeZero (N * 2011)] (v : Fin 14 → ℤ)
    (x : Fin 31 → ℕ) (c k digits : ZMod (N * 2011) → ℕ) (h : Facts v N x c k digits) :
    digits 0 &&& 3 = 0 := by
  simpa only [CurrentHighDigits2011.maskDigits_zero] using h.mask_tests 0

#print axioms polynomial_zero_window
#check Facts.source_rows
#check Facts.C_word
#check Facts.temporal_power
#check Facts.carry_equation
#check Facts.mask_tests

end DiophantineConsistency.CurrentPolynomialWindow2011Checks
