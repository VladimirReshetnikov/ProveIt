import ExponentialIdentities.TwoBaseIntegerExponent.SparsePowerCurve

namespace LeanProofs.TwoBaseIntegerExponent

open Polynomial

noncomputable section

private def shiftOne (P : Polynomial ℝ) : Polynomial ℝ :=
  P.comp (Polynomial.X + Polynomial.C 1)

@[simp] private theorem shiftOne_eval (P : Polynomial ℝ) (x : ℝ) :
    (shiftOne P).eval x = P.eval (x + 1) := by
  simp [shiftOne]

private theorem shiftOne_ne_zero {P : Polynomial ℝ} (hP : P ≠ 0) : shiftOne P ≠ 0 := by
  intro h
  apply hP
  have h' := congrArg (fun R : Polynomial ℝ ↦ R.comp (Polynomial.X - Polynomial.C 1)) h
  simpa [shiftOne, Polynomial.comp_assoc] using h'

private def decoderIndexEquiv (d : ℕ) :
    Fin (2 * d + 1 + 1) ≃ Fin (d + 1) ⊕ Fin (d + 1) :=
  (finCongr (by omega)).trans finSumFinEquiv.symm

private def decoderPairCode {d : ℕ} : Fin (d + 1) ⊕ Fin (d + 1) → ℕ × ℕ
  | Sum.inl j => (j, 0)
  | Sum.inr j => (j, 1)

private theorem decoderPairCode_injective {d : ℕ} :
    Function.Injective (decoderPairCode (d := d)) := by
  intro i j h
  cases i with
  | inl i =>
      cases j with
      | inl j => exact congrArg Sum.inl (Fin.ext (Prod.mk.inj h).1)
      | inr j => simp [decoderPairCode] at h
  | inr i =>
      cases j with
      | inl j => simp [decoderPairCode] at h
      | inr j => exact congrArg Sum.inr (Fin.ext (Prod.mk.inj h).1)

private def decoderPairs (d : ℕ) : Fin (2 * d + 1 + 1) → ℕ × ℕ :=
  decoderPairCode ∘ decoderIndexEquiv d

private theorem decoderPairs_injective (d : ℕ) : Function.Injective (decoderPairs d) :=
  decoderPairCode_injective.comp (decoderIndexEquiv d).injective

private def decoderCoefficients (d : ℕ) (A B : Polynomial ℝ) :
    Fin (2 * d + 1 + 1) → ℝ := fun i =>
  match decoderIndexEquiv d i with
  | Sum.inl j => A.coeff j
  | Sum.inr j => -B.coeff j

private theorem decoderCurve_left (j n : ℕ) :
    Real.exp (powerCurveFrequency logThreeDivLogTwo (j, 0) *
      ((n : ℝ) * Real.log 2)) = (((2 : ℝ) ^ n) ^ j) := by
  rw [show powerCurveFrequency logThreeDivLogTwo (j, 0) *
      ((n : ℝ) * Real.log 2) = ((n * j : ℕ) : ℝ) * Real.log 2 by
    simp [powerCurveFrequency]
    ring]
  rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [pow_mul]

private theorem logThreeDivLogTwo_mul_log_two :
    logThreeDivLogTwo * Real.log 2 = Real.log 3 := by
  rw [logThreeDivLogTwo]
  field_simp [ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))]

private theorem irrational_decoder_exponent : Irrational logThreeDivLogTwo := by
  apply irrational_of_not_integer_of_two_rpow_integer
  · rintro ⟨z, hz⟩
    have hz1R : (1 : ℝ) < (z : ℝ) := by
      rw [hz]
      exact one_lt_logThreeDivLogTwo
    have hz2R : (z : ℝ) < 2 := by
      rw [hz]
      linarith [logThreeDivLogTwo_lt_eight_fifths]
    have hz1 : (1 : ℤ) < z := by exact_mod_cast hz1R
    have hz2 : z < (2 : ℤ) := by exact_mod_cast hz2R
    omega
  · refine ⟨3, ?_⟩
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
      show Real.log 2 * logThreeDivLogTwo = Real.log 3 by
        rw [mul_comm, logThreeDivLogTwo_mul_log_two],
      Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    norm_num

private theorem decoderCurve_right (j n : ℕ) :
    Real.exp (powerCurveFrequency logThreeDivLogTwo (j, 1) *
      ((n : ℝ) * Real.log 2)) =
      ((3 : ℝ) ^ n) * (((2 : ℝ) ^ n) ^ j) := by
  rw [show powerCurveFrequency logThreeDivLogTwo (j, 1) *
      ((n : ℝ) * Real.log 2) =
        ((n * j : ℕ) : ℝ) * Real.log 2 + (n : ℝ) * Real.log 3 by
    simp only [powerCurveFrequency, Nat.cast_one, one_mul]
    rw [show (j : ℝ) + logThreeDivLogTwo = logThreeDivLogTwo + j by ring]
    rw [add_mul]
    rw [show logThreeDivLogTwo * ((n : ℝ) * Real.log 2) =
        (n : ℝ) * Real.log 3 by
      calc
        logThreeDivLogTwo * ((n : ℝ) * Real.log 2) =
            (n : ℝ) * (logThreeDivLogTwo * Real.log 2) := by ring
        _ = (n : ℝ) * Real.log 3 := by rw [logThreeDivLogTwo_mul_log_two]]
    norm_num [Nat.cast_mul]
    ring]
  rw [Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul,
    Real.exp_log (by norm_num : (0 : ℝ) < 2),
    Real.exp_log (by norm_num : (0 : ℝ) < 3)]
  rw [pow_mul]
  ring

private theorem shiftOne_natDegree_le {P : Polynomial ℝ} {d : ℕ}
    (hP : P.natDegree ≤ d) : (shiftOne P).natDegree ≤ d := by
  rw [shiftOne, Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C]
  simpa using hP

private theorem polynomial_eval_eq_fin_sum {P : Polynomial ℝ} {d : ℕ}
    (hP : P.natDegree ≤ d) (x : ℝ) :
    P.eval x = ∑ j : Fin (d + 1), P.coeff (j : ℕ) * x ^ (j : ℕ) := by
  rw [Polynomial.eval_eq_sum_range' (lt_of_le_of_lt hP (Nat.lt_succ_self d))]
  exact (Fin.sum_univ_eq_sum_range (fun j ↦ P.coeff j * x ^ j) (d + 1)).symm

private theorem decoderSparseSum_eq (d n : ℕ) (A B : Polynomial ℝ)
    (hA : A.natDegree ≤ d) (hB : B.natDegree ≤ d) :
    (∑ i : Fin (2 * d + 1 + 1),
      decoderCoefficients d A B i *
        Real.exp (powerCurveFrequency logThreeDivLogTwo (decoderPairs d i) *
          ((n : ℝ) * Real.log 2))) =
      A.eval ((2 : ℝ) ^ n) - (3 : ℝ) ^ n * B.eval ((2 : ℝ) ^ n) := by
  let g : Fin (d + 1) ⊕ Fin (d + 1) → ℝ
    | Sum.inl j => A.coeff j *
        Real.exp (powerCurveFrequency logThreeDivLogTwo ((j : ℕ), 0) *
          ((n : ℝ) * Real.log 2))
    | Sum.inr j => -B.coeff j *
        Real.exp (powerCurveFrequency logThreeDivLogTwo ((j : ℕ), 1) *
          ((n : ℝ) * Real.log 2))
  calc
    (∑ i : Fin (2 * d + 1 + 1),
      decoderCoefficients d A B i *
        Real.exp (powerCurveFrequency logThreeDivLogTwo (decoderPairs d i) *
          ((n : ℝ) * Real.log 2))) =
        ∑ s : Fin (d + 1) ⊕ Fin (d + 1), g s := by
          rw [← Equiv.sum_comp (decoderIndexEquiv d) g]
          apply Finset.sum_congr rfl
          intro i _
          generalize hs : decoderIndexEquiv d i = s
          cases s <;> simp [decoderCoefficients, decoderPairs, decoderPairCode,
            Function.comp_apply, g, hs]
    _ = (∑ j : Fin (d + 1), A.coeff j * (((2 : ℝ) ^ n) ^ (j : ℕ))) +
        ∑ j : Fin (d + 1), -B.coeff j *
          ((3 : ℝ) ^ n * (((2 : ℝ) ^ n) ^ (j : ℕ))) := by
          rw [Fintype.sum_sum_type]
          apply congrArg₂ (· + ·)
          · apply Finset.sum_congr rfl
            intro j _
            simp only [g]
            rw [decoderCurve_left]
          · apply Finset.sum_congr rfl
            intro j _
            simp only [g]
            rw [decoderCurve_right]
    _ = A.eval ((2 : ℝ) ^ n) - (3 : ℝ) ^ n * B.eval ((2 : ℝ) ^ n) := by
      rw [polynomial_eval_eq_fin_sum hA, polynomial_eval_eq_fin_sum hB]
      rw [sub_eq_add_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
      apply congrArg₂ (· + ·) rfl
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- A degree-`d` rational function cannot decode the synchronized observations
`2^n + 1` and `3^n + 1` at more than `2d+1` consecutive indices. -/
theorem rational_sum_decoder_card_le {L d : ℕ} (P Q : Polynomial ℝ)
    (hP : P.natDegree ≤ d) (hQ : Q.natDegree ≤ d) (hQne : Q ≠ 0)
    (hzero : ∀ n : Fin L,
      P.eval ((2 : ℝ) ^ (n : ℕ) + 1) =
        ((3 : ℝ) ^ (n : ℕ) + 1) * Q.eval ((2 : ℝ) ^ (n : ℕ) + 1)) :
    L ≤ 2 * d + 1 := by
  by_contra hbound
  have hlarge : 2 * d + 1 + 1 ≤ L := by omega
  let A : Polynomial ℝ := shiftOne (P - Q)
  let B : Polynomial ℝ := shiftOne Q
  have hPQ : (P - Q).natDegree ≤ d :=
    (Polynomial.natDegree_sub_le P Q).trans (max_le hP hQ)
  have hA : A.natDegree ≤ d := shiftOne_natDegree_le hPQ
  have hB : B.natDegree ≤ d := shiftOne_natDegree_le hQ
  have hz : StrictMono (fun i : Fin (2 * d + 1 + 1) ↦
      (i : ℝ) * Real.log 2) := by
    intro i j hij
    exact mul_lt_mul_of_pos_right (by exact_mod_cast hij)
      (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  have hrelation : ∀ i : Fin (2 * d + 1 + 1),
      ∑ j, decoderCoefficients d A B j *
        Real.exp (powerCurveFrequency logThreeDivLogTwo (decoderPairs d j) *
          ((i : ℝ) * Real.log 2)) = 0 := by
    intro i
    rw [decoderSparseSum_eq d (i : ℕ) A B hA hB]
    have hi := hzero (Fin.castLE hlarge i)
    have hAeval : A.eval ((2 : ℝ) ^ (i : ℕ)) =
        P.eval ((2 : ℝ) ^ (i : ℕ) + 1) -
          Q.eval ((2 : ℝ) ^ (i : ℕ) + 1) := by
      simp [A, shiftOne_eval]
    have hBeval : B.eval ((2 : ℝ) ^ (i : ℕ)) =
        Q.eval ((2 : ℝ) ^ (i : ℕ) + 1) := by
      simp [B, shiftOne_eval]
    rw [hAeval, hBeval]
    change P.eval ((2 : ℝ) ^ (i : ℕ) + 1) =
      ((3 : ℝ) ^ (i : ℕ) + 1) * Q.eval ((2 : ℝ) ^ (i : ℕ) + 1) at hi
    rw [hi]
    ring
  have hcoeff := sparsePowerCurve_coeff_eq_zero_of_zeros
    irrational_decoder_exponent (decoderPairs d) (decoderPairs_injective d)
    (decoderCoefficients d A B)
    (fun i : Fin (2 * d + 1 + 1) ↦ (i : ℝ) * Real.log 2) hz hrelation
  have hBzero : B = 0 := by
    ext k
    by_cases hk : k < d + 1
    · let j : Fin (d + 1) := ⟨k, hk⟩
      have hj := hcoeff ((decoderIndexEquiv d).symm (Sum.inr j))
      have : -B.coeff k = 0 := by
        simpa [decoderCoefficients, j] using hj
      simpa using neg_eq_zero.mp this
    · have hdk : d < k := by omega
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (hB.trans_lt hdk)
  exact (shiftOne_ne_zero hQne) hBzero

end

end LeanProofs.TwoBaseIntegerExponent
