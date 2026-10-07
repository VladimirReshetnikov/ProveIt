import OAI.Combinatorics.Progressions.Estimates.TranslationShearExponentialOver
import OAI.Combinatorics.Progressions.Estimates.WeightedTranslationShearExponential

namespace OAI

section

namespace Erdos3

open MvPolynomial

variable {σ R S : Type*} [CommRing R] [CommRing S]
  [Algebra ℚ R] [Algebra ℚ S] {w : σ ⊕ Unit → ℕ}

noncomputable def translationShearCoordinates
    (D : PolynomialShearLieAlgebra w R) (b : σ → R) (P : MvPolynomial σ R)
    (hb : ∀ i, D.val (X (Sum.inl i)) = C (b i))
    (hP : D.val (X (Sum.inr ())) = rename Sum.inl P) :
    PolynomialTranslationGroupOver R σ :=
  (existsUnique_translation_of_shear_exp D b P hb hP).exists.choose

theorem translationShearCoordinates_action
    (D : PolynomialShearLieAlgebra w R) (b : σ → R) (P : MvPolynomial σ R)
    (hb : ∀ i, D.val (X (Sum.inl i)) = C (b i))
    (hP : D.val (X (Sum.inr ())) = rename Sum.inl P) :
    PolynomialTranslationGroupOver.actionMonoidHom (translationShearCoordinates D b P hb hP) =
      (polynomialShearExpAut D).val :=
  (existsUnique_translation_of_shear_exp D b P hb hP).exists.choose_spec

theorem translationShearCoordinates_base
    (D : PolynomialShearLieAlgebra w R) (b : σ → R) (P : MvPolynomial σ R)
    (hb : ∀ i, D.val (X (Sum.inl i)) = C (b i))
    (hP : D.val (X (Sum.inr ())) = rename Sum.inl P) :
    (translationShearCoordinates D b P hb hP).base = b := by
  funext i
  have he := congrArg
    (fun f : MvPolynomial (σ ⊕ Unit) R ≃ₐ[R] MvPolynomial (σ ⊕ Unit) R =>
      f (X (Sum.inl i))) (translationShearCoordinates_action D b P hb hP)
  change PolynomialTranslationGroupOver.actionHom _ (X (Sum.inl i)) =
    polynomialShearExp D (X (Sum.inl i)) at he
  rw [PolynomialTranslationGroupOver.actionHom_X_inl,
    polynomialShearExp_X_of_derivation_eq_C D (Sum.inl i) (b i) (hb i)] at he
  exact MvPolynomial.C_injective (σ ⊕ Unit) R (add_left_cancel he)

theorem translationShearCoordinates_map_action
    (f : R →+* S) (D : PolynomialShearLieAlgebra w R)
    (b : σ → R) (P : MvPolynomial σ R)
    (hb : ∀ i, D.val (X (Sum.inl i)) = C (b i))
    (hP : D.val (X (Sum.inr ())) = rename Sum.inl P) :
    PolynomialTranslationGroupOver.actionMonoidHom
        (PolynomialTranslationGroupOver.map f (translationShearCoordinates D b P hb hP)) =
      (polynomialShearExpAut (polynomialShearMap f D)).val := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply MvPolynomial.algHom_ext
  intro i
  have he := congrArg
    (fun a : MvPolynomial (σ ⊕ Unit) R ≃ₐ[R] MvPolynomial (σ ⊕ Unit) R => a (X i))
    (translationShearCoordinates_action D b P hb hP)
  change PolynomialTranslationGroupOver.actionHom _ (X i) = polynomialShearExp D (X i) at he
  have hm := PolynomialTranslationGroupOver.map_actionHom f
    (translationShearCoordinates D b P hb hP) (X i)
  rw [he, polynomialShearExp_map, map_X] at hm
  exact hm.symm

omit [Algebra ℚ R] [Algebra ℚ S] in
theorem polynomialShearMap_translation_base
    (f : R →+* S) (D : PolynomialShearLieAlgebra w R) (b : σ → R)
    (hb : ∀ i, D.val (X (Sum.inl i)) = C (b i)) (i : σ) :
    (polynomialShearMap f D).val (X (Sum.inl i)) = C (f (b i)) := by
  rw [polynomialShearMap_X, hb, map_C]

omit [Algebra ℚ R] [Algebra ℚ S] in
theorem polynomialShearMap_translation_polynomial
    (f : R →+* S) (D : PolynomialShearLieAlgebra w R) (P : MvPolynomial σ R)
    (hP : D.val (X (Sum.inr ())) = rename Sum.inl P) :
    (polynomialShearMap f D).val (X (Sum.inr ())) = rename Sum.inl (MvPolynomial.map f P) := by
  rw [polynomialShearMap_X, hP, MvPolynomial.map_rename]

theorem translationShearCoordinates_map
    (f : R →+* S) (D : PolynomialShearLieAlgebra w R)
    (b : σ → R) (P : MvPolynomial σ R)
    (hb : ∀ i, D.val (X (Sum.inl i)) = C (b i))
    (hP : D.val (X (Sum.inr ())) = rename Sum.inl P) :
    PolynomialTranslationGroupOver.map f (translationShearCoordinates D b P hb hP) =
      translationShearCoordinates (polynomialShearMap f D) (fun i => f (b i))
        (MvPolynomial.map f P) (polynomialShearMap_translation_base f D b hb)
        (polynomialShearMap_translation_polynomial f D P hP) := by
  apply PolynomialTranslationGroupOver.actionMonoidHom_injective
  rw [translationShearCoordinates_map_action, translationShearCoordinates_action]

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

variable {σ R : Type*} [CommRing R] [Algebra ℚ R]

omit [Algebra ℚ R] in
theorem PolynomialTranslationGroupOver.action_inverse_X_inr
    (g : PolynomialTranslationGroupOver R σ) :
    (actionMonoidHom g).symm (X (Sum.inr ())) =
      X (Sum.inr ()) - rename Sum.inl g.polynomial := by
  have he : (actionMonoidHom g).symm = actionMonoidHom g⁻¹ :=
    (map_inv actionMonoidHom g).symm
  rw [he]
  change actionHom g⁻¹ (X (Sum.inr ())) = _
  rw [actionHom_X_inr]
  simp only [base_inv, polynomial_inv, map_neg, polynomialTranslate_comp_ring,
    neg_add_cancel, polynomialTranslate_zero_ring, sub_eq_add_neg]

theorem polynomialShearExpAut_neg_over {ι : Type*}
    (w : ι → ℕ) (d : ℕ) (hw : ∀ i, w i ≤ d)
    (D : PolynomialShearLieAlgebra w R) :
    polynomialShearExpAut (-D) = (polynomialShearExpAut D)⁻¹ := by
  exact (polynomialShearBCHEquivOver w d hw).map_inv
    (⟨D⟩ : (polynomialShearRatFiltration (R := R) w d hw).Group)

theorem translationShearCoordinates_inverse_exp
    (w : σ ⊕ Unit → ℕ) (d : ℕ) (hw : ∀ i, w i ≤ d)
    (D : PolynomialShearLieAlgebra w R) (b : σ → R) (P : MvPolynomial σ R)
    (hb : ∀ i, D.val (X (Sum.inl i)) = C (b i))
    (hP : D.val (X (Sum.inr ())) = rename Sum.inl P) :
    polynomialShearExp (-D) (X (Sum.inr ())) =
      X (Sum.inr ()) - rename Sum.inl (translationShearCoordinates D b P hb hP).polynomial := by
  rw [← polynomialShearExpAut_apply, polynomialShearExpAut_neg_over w d hw]
  have he := translationShearCoordinates_action D b P hb hP
  change ((polynomialShearExpAut D).val).symm (X (Sum.inr ())) = _
  rw [← he]
  exact PolynomialTranslationGroupOver.action_inverse_X_inr _

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

variable {σ R : Type*} [CommRing R]

noncomputable def translationBaseDerivative (b : σ → R) :
    Derivation R (MvPolynomial σ R) (MvPolynomial σ R) :=
  mkDerivation R (fun i => C (b i))

@[simp] theorem translationBaseDerivative_C (b : σ → R) (r : R) :
    translationBaseDerivative b (C r) = 0 := MvPolynomial.derivation_C _ _

@[simp] theorem translationBaseDerivative_X (b : σ → R) (i : σ) :
    translationBaseDerivative b (X i) = C (b i) := mkDerivation_X _ _ _

theorem translationBaseDerivative_apply [Fintype σ] (b : σ → R)
    (P : MvPolynomial σ R) :
    translationBaseDerivative b P = ∑ i, b i • pderiv i P := by
  classical
  have h : translationBaseDerivative b = ∑ i, b i • pderiv i := by
    apply MvPolynomial.derivation_ext
    intro j
    rw [translationBaseDerivative_X]
    change _ = (Derivation.coeFnAddMonoidHom (∑ i, b i • pderiv i)) (X j)
    rw [map_sum]
    simp [Finset.sum_apply, Derivation.coeFnAddMonoidHom_apply,
      MvPolynomial.pderiv_X, Pi.single_apply,
      MvPolynomial.C_eq_smul_one]
  rw [h]
  change (Derivation.coeFnAddMonoidHom (∑ i, b i • pderiv i)) P = _
  rw [map_sum]
  simp only [Finset.sum_apply, Derivation.coeFnAddMonoidHom_apply, Derivation.smul_apply]

theorem translationShear_derivation_rename_eq {w : σ ⊕ Unit → ℕ}
    (D : PolynomialShearLieAlgebra w R) (b : σ → R)
    (hb : ∀ i, D.val (X (Sum.inl i)) = C (b i)) (P : MvPolynomial σ R) :
    D.val (rename Sum.inl P) = rename Sum.inl (translationBaseDerivative b P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
    simp only [map_mul, rename_X, Derivation.leibniz, smul_eq_mul,
      hb, translationBaseDerivative_X, map_add, rename_C, hP]

theorem translationShear_derivation_pow_extra {w : σ ⊕ Unit → ℕ}
    (D : PolynomialShearLieAlgebra w R) (b : σ → R) (P : MvPolynomial σ R)
    (hb : ∀ i, D.val (X (Sum.inl i)) = C (b i))
    (hP : D.val (X (Sum.inr ())) = rename Sum.inl P) (k : ℕ) :
    (D.val.toLinearMap ^ (k + 1)) (X (Sum.inr ())) =
      rename Sum.inl (((translationBaseDerivative b).toLinearMap ^ k) P) := by
  induction k with
  | zero => simpa using hP
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, pow_succ', Module.End.mul_apply]
    exact translationShear_derivation_rename_eq D b hb _

variable [Algebra ℚ R]

theorem polynomialShear_neg_pow_apply {ι : Type*} {w : ι → ℕ}
    (D : PolynomialShearLieAlgebra w R) (k : ℕ) (Q : MvPolynomial ι R) :
    ((-D).val.toLinearMap ^ k) Q =
      (-1 : ℚ) ^ k • (D.val.toLinearMap ^ k) Q := by
  have h : (-D).val.toLinearMap = (-1 : ℚ) • D.val.toLinearMap := by
    change -D.val.toLinearMap = (-1 : ℚ) • D.val.toLinearMap
    exact (neg_one_smul ℚ D.val.toLinearMap).symm
  rw [h, smul_pow, LinearMap.smul_apply]

theorem translationShearCoordinates_polynomial_series
    (w : σ ⊕ Unit → ℕ) (d : ℕ) (hw : ∀ i, w i ≤ d)
    (D : PolynomialShearLieAlgebra w R) (b : σ → R) (P : MvPolynomial σ R)
    (hb : ∀ i, D.val (X (Sum.inl i)) = C (b i))
    (hP : D.val (X (Sum.inr ())) = rename Sum.inl P) :
    (translationShearCoordinates D b P hb hP).polynomial =
      ∑ k ∈ Finset.range (w (Sum.inr ())),
        ((-1 : ℚ) ^ k / ((k + 1).factorial : ℚ)) •
          ((translationBaseDerivative b).toLinearMap ^ k) P := by
  have he := translationShearCoordinates_inverse_exp w d hw D b P hb hP
  rw [polynomialShearExp_eq_sum (-D) (weightedSupportLE_X w (Sum.inr ())),
    Finset.sum_range_succ'] at he
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero,
    Module.End.one_apply, one_smul] at he
  have hs : (∑ k ∈ Finset.range (w (Sum.inr ())),
      (((k + 1).factorial : ℚ)⁻¹) •
        ((-D).val.toLinearMap ^ (k + 1)) (X (Sum.inr ()))) =
      -rename Sum.inl (∑ k ∈ Finset.range (w (Sum.inr ())),
        ((-1 : ℚ) ^ k / ((k + 1).factorial : ℚ)) •
          ((translationBaseDerivative b).toLinearMap ^ k) P) := by
    rw [map_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [polynomialShear_neg_pow_apply, translationShear_derivation_pow_extra D b P hb hP]
    rw [AlgHom.map_smul_of_tower, smul_smul, ← neg_smul]
    congr 1
    rw [pow_succ]
    ring
  rw [hs] at he
  apply MvPolynomial.rename_injective Sum.inl Sum.inl_injective
  apply neg_injective
  apply add_left_cancel (a := X (Sum.inr ()))
  simpa only [sub_eq_add_neg] using he.symm.trans (add_comm _ _)

end Erdos3

end

end OAI
