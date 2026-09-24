import Diophantine.Paper1982.Coding

/-!
# Jones 1982, §5: the shorter polynomial masks

Section 5 replaces the four-`L` series of §4 by `λ + Q = ∑_{i≤L} B^i`,
where `L = (δ+1)^(ν+1)` and `Q = B^L`. The resulting polynomial
`H = −c^δ D₀` has degree strictly less than `2L`. Its coefficient at `L`
still detects the original equation, and the same absolute coefficient
bound applies. These statements hold also for `δ = 0`.
-/

namespace Jones1982

open Polynomial Finset

variable (ν δ : ℕ)

/-- The series `λ + Q = ∑_{i≤L} X^i` used in (D12). -/
noncomputable def shortLampoly : ℤ[X] := ∑ i ∈ range (Lexp ν δ + 1), X ^ i

/-- The polynomial `D₀ = z(λ + Q) − e` of (D12). -/
noncomputable def shortD0poly (P : MvPolynomial (Fin (ν + 1)) ℤ) (z : ℕ) : ℤ[X] :=
  C (z : ℤ) * shortLampoly ν δ - epoly ν δ P z

/-- The polynomial `−c^δ D₀` whose middle coefficient detects a solution. -/
noncomputable def shortHpoly (P : MvPolynomial (Fin (ν + 1)) ℤ)
    (z : ℕ) (zs : Fin (ν + 1) → ℕ) : ℤ[X] :=
  -(cpoly ν δ zs ^ δ * shortD0poly ν δ P z)

theorem coeff_shortLampoly (i : ℕ) :
    (shortLampoly ν δ).coeff i = if i < Lexp ν δ + 1 then 1 else 0 := by
  unfold shortLampoly
  rw [finsetSum_coeff]
  simp only [coeff_X_pow]
  rw [Finset.sum_ite_eq]
  simp

/-- Shortening the series does not change any coefficient through position `L`. -/
theorem coeff_shortD0poly_eq_D0poly (P : MvPolynomial (Fin (ν + 1)) ℤ) (z i : ℕ)
    (hi : i ≤ Lexp ν δ) :
    (shortD0poly ν δ P z).coeff i = (D0poly ν δ P z).coeff i := by
  have hL : 0 < Lexp ν δ := by positivity
  unfold shortD0poly D0poly
  rw [coeff_sub, coeff_sub, coeff_C_mul, coeff_C_mul, coeff_shortLampoly, coeff_lampoly,
    if_pos (by omega : i < Lexp ν δ + 1), if_pos (by omega : i < 4 * Lexp ν δ)]

theorem coeff_shortD0poly_of_mem (P : MvPolynomial (Fin (ν + 1)) ℤ) (z : ℕ)
    {k : Fin (ν + 2) → ℕ} (hk : k ∈ star ν δ) :
    (shortD0poly ν δ P z).coeff (Lexp ν δ - expo ν δ k) = -Pcoef ν P k := by
  rw [coeff_shortD0poly_eq_D0poly ν δ P z _ (Nat.sub_le _ _)]
  exact coeff_D0_of_mem ν δ P z hk

/-- Every coefficient of the shorter `D₀` lies in `[-z,z]`. -/
theorem abs_coeff_shortD0poly_le (P : MvPolynomial (Fin (ν + 1)) ℤ) {z : ℕ}
    (hP : ∀ k ∈ star ν δ, |Pcoef ν P k| ≤ z) (i : ℕ) :
    |(shortD0poly ν δ P z).coeff i| ≤ z := by
  by_cases h : ∃ k ∈ star ν δ, Lexp ν δ - expo ν δ k = i
  · obtain ⟨k, hk, rfl⟩ := h
    rw [coeff_shortD0poly_of_mem ν δ P z hk, abs_neg]
    exact hP k hk
  · push Not at h
    unfold shortD0poly
    rw [coeff_sub, coeff_C_mul, coeff_shortLampoly, coeff_epoly_of_not ν δ P z h]
    split_ifs <;> simp

set_option maxHeartbeats 1000000 in
/-- The product's coefficients through `L` are unchanged by shortening the mask. -/
theorem coeff_shortHpoly_eq_Hpoly (P : MvPolynomial (Fin (ν + 1)) ℤ)
    (z : ℕ) (zs : Fin (ν + 1) → ℕ) (i : ℕ) (hi : i ≤ Lexp ν δ) :
    (shortHpoly ν δ P z zs).coeff i = (Hpoly ν δ P z zs).coeff i := by
  unfold shortHpoly Hpoly
  rw [coeff_neg, coeff_neg, coeff_mul, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply congrArg (fun x : ℤ => -x)
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [coeff_shortD0poly_eq_D0poly ν δ P z _ ((Nat.sub_le i a).trans hi)]

/-- The coefficient of `B^L` in the §5 polynomial is `δ! P(z₀,…,z_ν)`. -/
theorem coeff_shortHpoly_Lexp (P : MvPolynomial (Fin (ν + 1)) ℤ)
    (hP : P.totalDegree ≤ δ) (z : ℕ) (zs : Fin (ν + 1) → ℕ) :
    (shortHpoly ν δ P z zs).coeff (Lexp ν δ) =
      (δ.factorial : ℤ) * MvPolynomial.eval (fun j => (zs j : ℤ)) P := by
  exact (coeff_shortHpoly_eq_Hpoly ν δ P z zs _ le_rfl).trans
    (coeff_Hpoly_Lexp ν δ P hP z zs)

/-- The shorter product has the same absolute coefficient bound as in §4. -/
theorem abs_coeff_shortHpoly_le (P : MvPolynomial (Fin (ν + 1)) ℤ) {z : ℕ}
    (hP : ∀ k ∈ star ν δ, |Pcoef ν P k| ≤ z) (zs : Fin (ν + 1) → ℕ) (j : ℕ) :
    |(shortHpoly ν δ P z zs).coeff j| ≤ z * (1 + ∑ i, (zs i : ℤ)) ^ δ := by
  unfold shortHpoly
  rw [coeff_neg, abs_neg, coeff_mul]
  calc |∑ x ∈ Finset.HasAntidiagonal.antidiagonal j,
          (cpoly ν δ zs ^ δ).coeff x.1 * (shortD0poly ν δ P z).coeff x.2|
      ≤ ∑ x ∈ Finset.HasAntidiagonal.antidiagonal j,
          |(cpoly ν δ zs ^ δ).coeff x.1 * (shortD0poly ν δ P z).coeff x.2| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x ∈ Finset.HasAntidiagonal.antidiagonal j, (cpoly ν δ zs ^ δ).coeff x.1 * z := by
        apply Finset.sum_le_sum
        intro x _
        rw [abs_mul, abs_of_nonneg (coeff_cpoly_pow_nonneg ν δ zs _)]
        exact mul_le_mul_of_nonneg_left (abs_coeff_shortD0poly_le ν δ P hP _)
          (coeff_cpoly_pow_nonneg ν δ zs _)
    _ = (∑ a ∈ range (j + 1), (cpoly ν δ zs ^ δ).coeff a) * z := by
        rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_mul]
    _ ≤ (∑ a ∈ range (j + 1 + Lexp ν δ), (cpoly ν δ zs ^ δ).coeff a) * z := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
        intro a _ _
        exact coeff_cpoly_pow_nonneg ν δ zs a
    _ = z * (1 + ∑ i, (zs i : ℤ)) ^ δ := by
        rw [sum_coeff_cpoly_pow ν δ zs (by omega), mul_comm]

theorem natDegree_shortLampoly_le : (shortLampoly ν δ).natDegree ≤ Lexp ν δ := by
  unfold shortLampoly
  apply natDegree_sum_le_of_forall_le
  intro i hi
  have := Finset.mem_range.1 hi
  exact (natDegree_X_pow_le _).trans (by omega)

theorem natDegree_shortD0poly_le (P : MvPolynomial (Fin (ν + 1)) ℤ) (z : ℕ) :
    (shortD0poly ν δ P z).natDegree ≤ Lexp ν δ := by
  unfold shortD0poly
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · exact (natDegree_C_mul_le _ _).trans (natDegree_shortLampoly_le ν δ)
  · exact natDegree_epoly_le ν δ P z

/-- All nonzero coefficients fit into the `2L`-digit mask used in (D15). -/
theorem natDegree_shortHpoly_lt (P : MvPolynomial (Fin (ν + 1)) ℤ)
    (z : ℕ) (zs : Fin (ν + 1) → ℕ) :
    (shortHpoly ν δ P z zs).natDegree < 2 * Lexp ν δ := by
  unfold shortHpoly
  rw [natDegree_neg]
  have h1 : (cpoly ν δ zs ^ δ).natDegree ≤ δ * (δ + 1) ^ ν :=
    natDegree_pow_le.trans (Nat.mul_le_mul_left _ (natDegree_cpoly_le ν δ zs))
  have h2 : δ * (δ + 1) ^ ν < Lexp ν δ := by
    unfold Lexp
    rw [pow_succ]
    have : 0 < (δ + 1) ^ ν := by positivity
    nlinarith
  have := natDegree_mul_le (p := cpoly ν δ zs ^ δ) (q := shortD0poly ν δ P z)
  have := natDegree_shortD0poly_le ν δ P z
  omega

theorem eval_shortLampoly (B : ℤ) :
    (shortLampoly ν δ).eval B = ∑ i ∈ range (Lexp ν δ + 1), B ^ i := by
  unfold shortLampoly
  rw [eval_finsetSum]
  simp

/-- Splitting off the last term gives precisely `λ + Q` in (D12). -/
theorem eval_shortLampoly_split (B : ℤ) :
    (shortLampoly ν δ).eval B = (∑ i ∈ range (Lexp ν δ), B ^ i) + B ^ Lexp ν δ := by
  rw [eval_shortLampoly, Finset.sum_range_succ]

theorem eval_shortD0poly (P : MvPolynomial (Fin (ν + 1)) ℤ) (z : ℕ) (B : ℤ) :
    (shortD0poly ν δ P z).eval B =
      (z : ℤ) * (∑ i ∈ range (Lexp ν δ + 1), B ^ i) - (epoly ν δ P z).eval B := by
  unfold shortD0poly
  rw [eval_sub, eval_mul, eval_C, eval_shortLampoly]

theorem eval_shortHpoly (P : MvPolynomial (Fin (ν + 1)) ℤ) (z : ℕ)
    (zs : Fin (ν + 1) → ℕ) (B : ℤ) :
    (shortHpoly ν δ P z zs).eval B =
      -((cpoly ν δ zs).eval B ^ δ *
        ((z : ℤ) * (∑ i ∈ range (Lexp ν δ + 1), B ^ i) - (epoly ν δ P z).eval B)) := by
  unfold shortHpoly
  rw [eval_neg, eval_mul, eval_pow, eval_shortD0poly]

end Jones1982
