import OAI.Combinatorics.Progressions.Polynomial.PolynomialShearAffineExponential

namespace OAI

section

namespace Erdos3

open MvPolynomial

variable {R σ : Type*} [CommRing R] [Algebra ℚ R]
  {w : σ ⊕ Unit → ℕ}

omit [Algebra ℚ R] in
theorem translationShear_derivation_rename
    (D : PolynomialShearLieAlgebra w R) (b : σ → R)
    (hb : ∀ i, D.val (X (Sum.inl i)) = C (b i)) (P : MvPolynomial σ R) :
    ∃ Q : MvPolynomial σ R, D.val (rename Sum.inl P) = rename Sum.inl Q := by
  induction P using MvPolynomial.induction_on with
  | C c => exact ⟨0, by simp⟩
  | add P Q hP hQ =>
      obtain ⟨P', hP'⟩ := hP
      obtain ⟨Q', hQ'⟩ := hQ
      exact ⟨P' + Q', by simp only [map_add, hP', hQ']⟩
  | mul_X P i hP =>
      obtain ⟨P', hP'⟩ := hP
      refine ⟨P * C (b i) + X i * P', ?_⟩
      simp only [map_mul, rename_X, D.val.leibniz, hb, hP', smul_eq_mul,
        map_add, rename_C]

theorem translationShear_exp_extra_coordinate
    (D : PolynomialShearLieAlgebra w R) (b : σ → R) (P : MvPolynomial σ R)
    (hb : ∀ i, D.val (X (Sum.inl i)) = C (b i))
    (hP : D.val (X (Sum.inr ())) = rename Sum.inl P) :
    ∃ Q : MvPolynomial σ R,
      polynomialShearExp D (X (Sum.inr ())) = X (Sum.inr ()) + rename Sum.inl Q := by
  classical
  let S : Submodule R (MvPolynomial (σ ⊕ Unit) R) :=
    LinearMap.range (rename (R := R) (Sum.inl : σ → σ ⊕ Unit)).toLinearMap
  have hpow (k : ℕ) : (D.val.toLinearMap ^ (k + 1)) (X (Sum.inr ())) ∈ S := by
    induction k with
    | zero => exact ⟨P, by simpa using hP.symm⟩
    | succ k ih =>
        obtain ⟨Q, hQ⟩ := ih
        obtain ⟨Q', hQ'⟩ := translationShear_derivation_rename D b hb Q
        refine ⟨Q', ?_⟩
        rw [pow_succ', Module.End.mul_apply, ← hQ]
        exact hQ'.symm
  have hmem : polynomialShearExp D (X (Sum.inr ())) - X (Sum.inr ()) ∈ S := by
    rw [polynomialShearExp_eq_sum D (weightedSupportLE_X w (Sum.inr ())),
      Finset.sum_range_succ']
    simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, Module.End.one_apply,
      one_smul, add_sub_cancel_right]
    apply (S.restrictScalars ℚ).sum_mem
    intro k hk
    exact (S.restrictScalars ℚ).smul_mem _ (hpow k)
  obtain ⟨Q, hQ⟩ := hmem
  refine ⟨Q, ?_⟩
  change rename Sum.inl Q = polynomialShearExp D (X (Sum.inr ())) - X (Sum.inr ()) at hQ
  rw [hQ]
  abel

theorem existsUnique_translation_of_shear_exp
    (D : PolynomialShearLieAlgebra w R) (b : σ → R) (P : MvPolynomial σ R)
    (hb : ∀ i, D.val (X (Sum.inl i)) = C (b i))
    (hP : D.val (X (Sum.inr ())) = rename Sum.inl P) :
    ∃! g : PolynomialTranslationGroupOver R σ,
      PolynomialTranslationGroupOver.actionMonoidHom g = (polynomialShearExpAut D).val := by
  obtain ⟨Q, hQ⟩ := translationShear_exp_extra_coordinate D b P hb hP
  apply PolynomialTranslationGroupOver.existsUnique_action_of_shape
    (polynomialShearExpAut D).val b Q
  · intro i
    exact polynomialShearExp_X_of_derivation_eq_C D (Sum.inl i) (b i) (hb i)
  · exact hQ

end Erdos3

end

end OAI
