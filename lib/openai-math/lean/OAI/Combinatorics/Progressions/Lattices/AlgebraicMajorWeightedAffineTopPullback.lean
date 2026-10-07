import OAI.Combinatorics.Progressions.Polynomial.MajorTranslationPolynomialSymbolDegree
import OAI.Combinatorics.Progressions.Polynomial.TranslationPhaseQuotient
import OAI.Combinatorics.Progressions.Polynomial.TranslationTopDegree

namespace OAI

section

namespace Erdos3
open MvPolynomial

variable {U B : Type*}

noncomputable def majorSlowDilationPullback (q : ℕ) (H T : U → ℝ)
    (S : MvPolynomial (U ⊕ B) ℝ) : MvPolynomial (U ⊕ B) ℝ :=
  scaleMvPolynomialAxes
    (Sum.elim (fun i => H i / ((q : ℝ) * T i)) (fun _ : B => 1)) S

 theorem majorSlowDilationPullback_eval (q : ℕ) (hq : 0 < q) (H T : U → ℝ)
    (hH : ∀ i, 0 < H i) (hT : ∀ i, 0 < T i)
    (S : MvPolynomial (U ⊕ B) ℝ) (u : U → ℝ) (z : B → ℝ) :
    eval (Sum.elim (fun i => u i / H i) z) (majorSlowDilationPullback q H T S) =
      eval (Sum.elim (fun i => (u i / (q : ℝ)) / T i) z) S := by
  rw [majorSlowDilationPullback, scaleMvPolynomialAxes_eval]
  apply congrArg (fun x : U ⊕ B → ℝ => eval x S)
  funext j
  cases j with
  | inl i =>
    dsimp only [Sum.elim_inl]
    field_simp [(hH i).ne', (hT i).ne', (Nat.cast_pos.mpr hq : (0 : ℝ) < q).ne']
  | inr j => simp only [Sum.elim_inr, one_mul]

 theorem majorSlowDilationPullback_totalDegree_le (q : ℕ) (H T : U → ℝ)
    (S : MvPolynomial (U ⊕ B) ℝ) :
    (majorSlowDilationPullback q H T S).totalDegree ≤ S.totalDegree :=
  scaleMvPolynomialAxes_totalDegree_le _ _

theorem algebraic_major_dilation_pullback_identity
    (K : Submodule ℝ (B → ℝ)) (D : MvPolynomial (U ⊕ B) ℝ)
    (A : B → MvPolynomial U ℝ) (S : MvPolynomial (U ⊕ B) ℝ)
    (R : MvPolynomial (U ⊕ B) ℚ) (q : ℕ) (hq : 0 < q)
    (H T : U → ℝ) (hH : ∀ i, 0 < H i) (hT : ∀ i, 0 < T i)
    (hsource : ∀ (v : U → ℝ) (b : B → ℝ), b ∈ K →
      eval (Sum.elim (fun i => (q : ℝ) * v i) b) D =
        eval (Sum.elim (fun i => v i / T i)
          (fun j => b j - eval (fun i => (q : ℝ) * v i) (A j))) S +
        eval₂ (algebraMap ℚ ℝ) (Sum.elim v b) R)
    (u : U → ℝ) (b : B → ℝ) (hb : b ∈ K) :
    eval (Sum.elim u b) D =
      eval (Sum.elim (fun i => u i / H i) (fun j => b j - eval u (A j)))
        (majorSlowDilationPullback q H T S) +
      eval₂ (algebraMap ℚ ℝ) (Sum.elim u b) (jointRationalPolynomialDilation q R) := by
  rw [majorSlowDilationPullback_eval q hq H T hH hT,
    jointRationalPolynomialDilation_eval₂]
  have hcancel : (fun i => (q : ℝ) * (u i / (q : ℝ))) = u := by
    funext i
    exact mul_div_cancel₀ (u i) (Nat.cast_ne_zero.mpr hq.ne')
  simpa only [hcancel] using hsource (fun i => u i / (q : ℝ)) b hb

 theorem majorSlowDilationPullback_mass_le (q : ℕ) (hq : 0 < q) (H T : U → ℝ)
    (hH : ∀ i, 0 < H i) (hT : ∀ i, 0 < T i)
    (S : MvPolynomial (U ⊕ B) ℝ) {c : ℝ} (hc : 1 ≤ c)
    (hHT : ∀ i, H i ≤ c * (q : ℝ) * T i) {d : ℕ} (hS : S.totalDegree ≤ d) :
    realPolynomialMass (majorSlowDilationPullback q H T S) ≤ c^d * realPolynomialMass S := by
  apply jointPolynomialDilation_mass_le _ S hc _ hS
  intro i
  have hqT : 0 < (q : ℝ) * T i := mul_pos (Nat.cast_pos.mpr hq) (hT i)
  rw [abs_of_nonneg (div_nonneg (hH i).le hqT.le)]
  apply (div_le_iff₀ hqT).mpr
  simpa only [mul_assoc] using hHT i

theorem algebraic_major_dilation_pullback_decomposition
    (K : Submodule ℝ (B → ℝ)) (D : MvPolynomial (U ⊕ B) ℝ)
    (A : B → MvPolynomial U ℝ) (S : MvPolynomial (U ⊕ B) ℝ)
    (R : MvPolynomial (U ⊕ B) ℚ) (q : ℕ) (hq : 0 < q)
    (H T : U → ℝ) (hH : ∀ i, 0 < H i) (hT : ∀ i, 0 < T i)
    (hsource : ∀ (v : U → ℝ) (b : B → ℝ), b ∈ K →
      eval (Sum.elim (fun i => (q : ℝ) * v i) b) D =
        eval (Sum.elim (fun i => v i / T i)
          (fun j => b j - eval (fun i => (q : ℝ) * v i) (A j))) S +
        eval₂ (algebraMap ℚ ℝ) (Sum.elim v b) R)
    (c C : ℝ) (hc : 1 ≤ c) (hHT : ∀ i, H i ≤ c * (q : ℝ) * T i)
    (d l : ℕ) (hS : S.totalDegree ≤ d) (hR : R.totalDegree ≤ d)
    (hSmass : realPolynomialMass S ≤ C)
    (hRgrid : (fun α => R.coeff α) ∈ denominatorGrid l) :
    ∃ (S' : MvPolynomial (U ⊕ B) ℝ) (R' : MvPolynomial (U ⊕ B) ℚ),
      (∀ (u : U → ℝ) (b : B → ℝ), b ∈ K →
        eval (Sum.elim u b) D =
          eval (Sum.elim (fun i => u i / H i) (fun j => b j - eval u (A j))) S' +
          eval₂ (algebraMap ℚ ℝ) (Sum.elim u b) R') ∧
      realPolynomialMass S' ≤ c^d * C ∧ S'.totalDegree ≤ d ∧ R'.totalDegree ≤ d ∧
      (fun α => R'.coeff α) ∈ denominatorGrid (q^d*l) := by
  refine ⟨majorSlowDilationPullback q H T S, jointRationalPolynomialDilation q R,
    algebraic_major_dilation_pullback_identity K D A S R q hq H T hH hT hsource, ?_,
    (majorSlowDilationPullback_totalDegree_le q H T S).trans hS,
    (jointRationalPolynomialDilation_totalDegree_le q R).trans hR, ?_⟩
  · exact (majorSlowDilationPullback_mass_le q hq H T hH hT S hc hHT hS).trans
      (mul_le_mul_of_nonneg_left hSmass (pow_nonneg (le_trans zero_le_one hc) d))
  · exact jointRationalPolynomialDilation_denominatorGrid R q l d hq hR hRgrid

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

variable {U B : Type*}

theorem majorSlowDilationPullback_mem_weightedSupportLE
    (q : ℕ) (H T : U → ℝ) (S : MvPolynomial (U ⊕ B) ℝ)
    (w : U ⊕ B → ℕ) (d : ℕ) (hS : S ∈ weightedSupportLE w d) :
    majorSlowDilationPullback q H T S ∈ weightedSupportLE w d :=
  scaleMvPolynomialAxes_mem_weightedSupportLE _ w d hS

theorem algebraic_major_weighted_dilation_pullback_decomposition
    (w : B → ℕ) (hw : ∀ i, 0 < w i)
    (K : Submodule ℝ (B → ℝ)) (D : MvPolynomial (U ⊕ B) ℝ)
    (A : B → MvPolynomial U ℝ) (S : MvPolynomial (U ⊕ B) ℝ)
    (R : MvPolynomial (U ⊕ B) ℚ) (q : ℕ) (hq : 0 < q)
    (H T : U → ℝ) (hH : ∀ i, 0 < H i) (hT : ∀ i, 0 < T i)
    (hsource : ∀ (v : U → ℝ) (b : B → ℝ), b ∈ K →
      eval (Sum.elim (fun i => (q : ℝ) * v i) b) D =
        eval (Sum.elim (fun i => v i / T i)
          (fun j => b j - eval (fun i => (q : ℝ) * v i) (A j))) S +
        eval₂ (algebraMap ℚ ℝ) (Sum.elim v b) R)
    (c C : ℝ) (hc : 1 ≤ c) (hHT : ∀ i, H i ≤ c * (q : ℝ) * T i)
    (d l : ℕ)
    (hS : S ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (hR : R ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (hSmass : realPolynomialMass S ≤ C)
    (hRgrid : (fun α => R.coeff α) ∈ denominatorGrid l) :
    ∃ (S' : MvPolynomial (U ⊕ B) ℝ) (R' : MvPolynomial (U ⊕ B) ℚ),
      S' = majorSlowDilationPullback q H T S ∧
      R' = jointRationalPolynomialDilation q R ∧
      (∀ (u : U → ℝ) (b : B → ℝ), b ∈ K →
        eval (Sum.elim u b) D =
          eval (Sum.elim (fun i => u i / H i) (fun j => b j - eval u (A j))) S' +
          eval₂ (algebraMap ℚ ℝ) (Sum.elim u b) R') ∧
      realPolynomialMass S' ≤ c^d * C ∧
      S' ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d ∧
      R' ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d ∧
      S'.totalDegree ≤ d ∧ R'.totalDegree ≤ d ∧
      (fun α => R'.coeff α) ∈ denominatorGrid (q^d*l) := by
  have hpos : ∀ i : U ⊕ B, 0 < Sum.elim (fun _ : U => 1) w i :=
    Sum.rec (fun _ => Nat.zero_lt_one) hw
  have hSdeg := weightedSupportLE_totalDegree_le_of_pos hpos hS
  have hRdeg := weightedSupportLE_totalDegree_le_of_pos hpos hR
  have hS' := majorSlowDilationPullback_mem_weightedSupportLE q H T S _ d hS
  have hR' := jointRationalPolynomialDilation_mem_weightedSupportLE q R _ d hR
  refine ⟨majorSlowDilationPullback q H T S, jointRationalPolynomialDilation q R,
    rfl, rfl,
    algebraic_major_dilation_pullback_identity K D A S R q hq H T hH hT hsource,
    ?_, hS', hR', weightedSupportLE_totalDegree_le_of_pos hpos hS',
    weightedSupportLE_totalDegree_le_of_pos hpos hR', ?_⟩
  · exact (majorSlowDilationPullback_mass_le q hq H T hH hT S hc hHT hSdeg).trans
      (mul_le_mul_of_nonneg_left hSmass (pow_nonneg (le_trans zero_le_one hc) d))
  · exact jointRationalPolynomialDilation_denominatorGrid R q l d hq hRdeg hRgrid

end Erdos3

end

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators TensorProduct

variable {U R : Type*} [CommRing R]

theorem homogeneousComponent_polynomialTranslate (h : ℕ) (r : U → R)
    (P : MvPolynomial U R) (hP : P.totalDegree ≤ h) :
    homogeneousComponent h (polynomialTranslate r P) = homogeneousComponent h P := by
  have hp : VectorPolynomial.DegreeLE (1 : U → ℕ) h (P ⊗ₜ[R] (1 : R)) := by
    intro α hα
    have hz : P.coeff α = 0 := coeff_eq_zero_of_totalDegree_lt (hP.trans_lt (by
      simpa only [Finsupp.weight_apply, Finsupp.sum, Pi.one_apply,
        smul_eq_mul, mul_one] using hα))
    simp only [VectorPolynomial.coefficients_tmul, hz, zero_smul]
  have ht := VectorPolynomial.homogeneousPart_translate r (P ⊗ₜ[R] (1 : R)) hp
  ext α
  have hc := congrArg (fun p => VectorPolynomial.coefficients p α) ht
  simpa only [VectorPolynomial.translate_tmul, VectorPolynomial.homogeneousPart_tmul,
    VectorPolynomial.coefficients_tmul, smul_eq_mul, mul_one] using hc

theorem polynomial_dilation_monomial (a c : R) (α : U →₀ ℕ) :
    aeval (fun i => C a * X i) (monomial α c) = monomial α (a ^ α.degree * c) := by
  classical
  rw [aeval_monomial]
  simp only [algebraMap_eq, Finsupp.prod, mul_pow, Finset.prod_mul_distrib,
    ← map_pow, ← map_prod, Finset.prod_pow_eq_pow_sum, prod_X_pow_eq_monomial]
  rw [monomial_eq, monomial_eq]
  simp only [map_one, one_mul, map_mul]
  have hd : (∑ i ∈ α.support, α i) = α.degree := rfl
  rw [hd]
  ring

theorem coeff_polynomial_dilation (a : R) (P : MvPolynomial U R) (α : U →₀ ℕ) :
    (aeval (fun i => C a * X i) P).coeff α = a ^ α.degree * P.coeff α := by
  classical
  conv_lhs => rw [P.as_sum]
  simp only [map_sum, polynomial_dilation_monomial, coeff_sum, coeff_monomial]
  by_cases hα : α ∈ P.support
  · rw [Finset.sum_eq_single α]
    · simp
    · intro β hβ hβα
      simp [hβα]
    · exact fun h => (h hα).elim
  · rw [Finset.sum_eq_zero]
    · have hz : P.coeff α = 0 := not_ne_iff.mp (fun h => hα (mem_support_iff.mpr h))
      simp only [hz, mul_zero]
    · intro β hβ
      have hβα : β ≠ α := by rintro rfl; exact hα hβ
      simp [hβα]

theorem homogeneousComponent_polynomial_dilation (h : ℕ) (a : R)
    (P : MvPolynomial U R) :
    homogeneousComponent h (aeval (fun i => C a * X i) P) =
      C (a ^ h) * homogeneousComponent h P := by
  classical
  ext α
  rw [coeff_homogeneousComponent, coeff_polynomial_dilation, coeff_C_mul,
    coeff_homogeneousComponent]
  by_cases hα : α.degree = h
  · simp only [hα, ite_true]
  · simp only [hα, ite_false, mul_zero]

theorem residueAffinePolynomial_eq_dilation_translate (q : ℕ) (r : U → ℤ)
    (P : MvPolynomial U ℝ) :
    residueAffinePolynomial q r P =
      aeval (fun i => C (q : ℝ) * X i) (polynomialTranslate (fun i => (r i : ℝ)) P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [residueAffinePolynomial]
  | add P Q hP hQ =>
    simpa only [residueAffinePolynomial, map_add] using congrArg₂ (· + ·) hP hQ
  | mul_X P i hP =>
    simp only [residueAffinePolynomial, map_mul, eval₂Hom_X', polynomialTranslate_X,
      map_add, aeval_X, aeval_C, algebraMap_eq] at *
    rw [hP, add_comm (C (r i : ℝ))]

theorem residueAffinePolynomial_homogeneousComponent (q h : ℕ) (r : U → ℤ)
    (P : MvPolynomial U ℝ) (hP : P.totalDegree ≤ h) :
    homogeneousComponent h (residueAffinePolynomial q r P) =
      C ((q : ℝ) ^ h) * homogeneousComponent h P := by
  rw [residueAffinePolynomial_eq_dilation_translate,
    homogeneousComponent_polynomial_dilation, homogeneousComponent_polynomialTranslate h _ P hP]

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

variable {U : Type*}

theorem residueAffinePolynomial_homogeneousComponent_eval
    (q h : ℕ) (r : U → ℤ) (P : MvPolynomial U ℝ)
    (hP : P.totalDegree ≤ h) (v : U → ℝ) :
    eval v (homogeneousComponent h (residueAffinePolynomial q r P)) =
      eval (fun i => (q : ℝ) * v i) (homogeneousComponent h P) := by
  have hdil : C ((q : ℝ) ^ h) * homogeneousComponent h P =
      aeval (fun i => C (q : ℝ) * X i) (homogeneousComponent h P) := by
    classical
    ext α
    rw [coeff_C_mul, coeff_polynomial_dilation, coeff_homogeneousComponent]
    by_cases hα : α.degree = h
    · simp only [hα, ite_true]
    · simp only [hα, ite_false, mul_zero]
  rw [residueAffinePolynomial_homogeneousComponent q h r P hP, hdil]
  change (aeval v) (aeval (fun i => C (q : ℝ) * X i)
    (homogeneousComponent h P)) = _
  rw [comp_aeval_apply]
  simp only [map_mul, aeval_C, aeval_X, Algebra.algebraMap_self, RingHom.id_apply,
    aeval_eq_eval]

theorem residueAffinePolynomial_weightedHomogeneousComponent_eval
    (q h : ℕ) (r : U → ℤ) (P : MvPolynomial U ℝ)
    (hP : P.totalDegree ≤ h) (v : U → ℝ) :
    eval v (weightedHomogeneousComponent (fun _ : U => 1) h
      (residueAffinePolynomial q r P)) =
      eval (fun i => (q : ℝ) * v i)
        (weightedHomogeneousComponent (fun _ : U => 1) h P) :=
  residueAffinePolynomial_homogeneousComponent_eval q h r P hP v

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

variable {U B : Type*}

noncomputable def jointResidueAffinePolynomial (q : ℕ) (r : U → ℤ)
    (D : MvPolynomial (U ⊕ B) ℝ) : MvPolynomial (U ⊕ B) ℝ :=
  aeval (Sum.elim (fun i => C (r i : ℝ) + C (q : ℝ) * X (Sum.inl i))
    (fun j => X (Sum.inr j))) D

theorem jointResidueAffinePolynomial_eval (q : ℕ) (r : U → ℤ)
    (D : MvPolynomial (U ⊕ B) ℝ) (u : U → ℝ) (b : B → ℝ) :
    eval (Sum.elim u b) (jointResidueAffinePolynomial q r D) =
      eval (Sum.elim (fun i => (r i : ℝ) + (q : ℝ) * u i) b) D := by
  induction D using MvPolynomial.induction_on with
  | C c => simp [jointResidueAffinePolynomial]
  | add D E hD hE => simpa only [jointResidueAffinePolynomial, map_add] using congrArg₂ (· + ·) hD hE
  | mul_X D i hD =>
    cases i <;> simp [jointResidueAffinePolynomial, map_mul] at hD ⊢ <;> rw [hD] <;> simp

private theorem jointResidueAffine_variables_degree (w : B → ℕ) (q : ℕ) (r : U → ℤ)
    (i : U ⊕ B) :
    Sum.elim (fun j => C (r j : ℝ) + C (q : ℝ) * X (Sum.inl j))
      (fun j => X (Sum.inr j)) i ∈
      weightedSupportLE (Sum.elim (fun _ : U => 1) w) (Sum.elim (fun _ : U => 1) w i) := by
  cases i with
  | inl i =>
    apply (weightedSupportLE _ _).add_mem (weightedSupportLE_C _ _ _)
    simpa only [zero_add] using weightedSupportLE_mul
      (weightedSupportLE_C (Sum.elim (fun _ : U => 1) w) 0 (q : ℝ))
      (weightedSupportLE_X (Sum.elim (fun _ : U => 1) w) (Sum.inl i))
  | inr j => exact weightedSupportLE_X (Sum.elim (fun _ : U => 1) w) (Sum.inr j)

theorem jointResidueAffinePolynomial_degree (w : B → ℕ) (q : ℕ) (r : U → ℤ)
    {d : ℕ} {D : MvPolynomial (U ⊕ B) ℝ}
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d) :
    jointResidueAffinePolynomial q r D ∈
      weightedSupportLE (Sum.elim (fun _ : U => 1) w) d :=
  weightedSupportLE_aeval _ _ _ (jointResidueAffine_variables_degree w q r) hD

theorem jointResidueAffinePolynomial_sub_axes_lower (w : B → ℕ) (q : ℕ) (r : U → ℤ)
    {d : ℕ} {D : MvPolynomial (U ⊕ B) ℝ}
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d) :
    jointResidueAffinePolynomial q r D -
      scaleMvPolynomialAxes (Sum.elim (fun _ : U => (q : ℝ)) (fun _ : B => 1)) D ∈
      weightedSupportLT (Sum.elim (fun _ : U => 1) w) d := by
  let v := Sum.elim (fun _ : U => 1) w
  let F : MvPolynomial (U ⊕ B) ℝ →ₐ[ℝ] MvPolynomial (U ⊕ B) ℝ := aeval (R := ℝ) (Sum.elim
    (fun i => C (r i : ℝ) + C (q : ℝ) * X (Sum.inl i)) (fun j => X (Sum.inr j)))
  let T := Sum.elim (fun _ : U => (q : ℝ)) (fun _ : B => 1)
  let G := aeval (R := ℝ) (fun i : U ⊕ B => C (T i) * X i)
  have hF : ∀ i, F (X i) ∈ weightedSupportLE v (v i) := by
    intro i
    simpa only [F, aeval_X] using jointResidueAffine_variables_degree w q r i
  have hG : ∀ i, G (X i) ∈ weightedSupportLE v (v i) := by
    intro i
    simpa only [G, aeval_X, zero_add] using
      weightedSupportLE_mul (weightedSupportLE_C v 0 (T i)) (weightedSupportLE_X v i)
  have hdiff : ∀ i, F (X i) - G (X i) ∈ weightedSupportLT v (v i) := by
    intro i
    cases i with
    | inl i =>
      simp only [F, G, T, aeval_X, Sum.elim_inl, add_sub_cancel_right]
      exact weightedSupportLE_lt_succ (weightedSupportLE_C v 0 (r i : ℝ))
    | inr j =>
      simp only [F, G, T, aeval_X, Sum.elim_inr, map_one, one_mul, sub_self]
      exact Submodule.zero_mem _
  rw [scaleMvPolynomialAxes_eq_aeval]
  exact weightedComparison_difference v v F G hF hG hdiff hD

theorem jointResidueAffinePolynomial_weightedHomogeneousComponent (w : B → ℕ)
    (q d : ℕ) (r : U → ℤ) (D : MvPolynomial (U ⊕ B) ℝ)
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d) :
    weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d
        (jointResidueAffinePolynomial q r D) =
      scaleMvPolynomialAxes (Sum.elim (fun _ : U => (q : ℝ)) (fun _ : B => 1))
        (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d D) := by
  have hlower := jointResidueAffinePolynomial_sub_axes_lower w q r hD
  have hzero : weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d
      (jointResidueAffinePolynomial q r D -
        scaleMvPolynomialAxes (Sum.elim (fun _ : U => (q : ℝ)) (fun _ : B => 1)) D) = 0 :=
    weightedHomogeneousComponent_eq_zero' d _ (fun α hα => (hlower hα).ne)
  rw [map_sub, sub_eq_zero] at hzero
  rw [hzero, scaleMvPolynomialAxes_weightedHomogeneousComponent]

end Erdos3

end

section

namespace Erdos3
open MvPolynomial

variable {U B : Type*}

 theorem jointResidueAffinePolynomial_weightedHomogeneousComponent_eval
    (w : B → ℕ) (q d : ℕ) (r : U → ℤ) (D : MvPolynomial (U ⊕ B) ℝ)
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (v : U → ℝ) (b : B → ℝ) :
    eval (Sum.elim v b)
      (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d
        (jointResidueAffinePolynomial q r D)) =
    eval (Sum.elim (fun i => (q : ℝ) * v i) b)
      (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d D) := by
  rw [jointResidueAffinePolynomial_weightedHomogeneousComponent w q d r D hD,
    scaleMvPolynomialAxes_eval]
  apply congrArg (fun x : U ⊕ B → ℝ => eval x _)
  funext i
  cases i <;> simp only [Sum.elim_inl, Sum.elim_inr, one_mul]

theorem algebraic_major_affine_top_dilation_identity
    (K : Submodule ℝ (B → ℝ)) (w : B → ℕ) (n : ℕ)
    (D : MvPolynomial (U ⊕ B) ℝ)
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) n)
    (A : B → MvPolynomial U ℝ) (hA : ∀ j, (A j).totalDegree ≤ w j)
    (S : MvPolynomial (U ⊕ B) ℝ) (R : MvPolynomial (U ⊕ B) ℚ)
    (q : ℕ) (r : U → ℤ) (T : U → ℝ)
    (hsource : ∀ (v : U → ℝ) (b : B → ℝ), b ∈ K →
      eval (Sum.elim v b)
        (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) n
          (jointResidueAffinePolynomial q r D)) =
      eval (Sum.elim (fun i => v i / T i)
        (fun j => b j - eval v
          (majorTranslationTopCoordinates w (fun j => residueAffinePolynomial q r (A j)) j))) S +
      eval₂ (algebraMap ℚ ℝ) (Sum.elim v b) R)
    (v : U → ℝ) (b : B → ℝ) (hb : b ∈ K) :
    eval (Sum.elim (fun i => (q : ℝ) * v i) b)
      (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) n D) =
    eval (Sum.elim (fun i => v i / T i)
      (fun j => b j - eval (fun i => (q : ℝ) * v i) (majorTranslationTopCoordinates w A j))) S +
    eval₂ (algebraMap ℚ ℝ) (Sum.elim v b) R := by
  have h := hsource v b hb
  rw [jointResidueAffinePolynomial_weightedHomogeneousComponent_eval w q n r D hD] at h
  simp only [majorTranslationTopCoordinates,
    residueAffinePolynomial_weightedHomogeneousComponent_eval q _ r _ (hA _)] at h
  exact h

theorem algebraic_major_affine_top_pullback_decomposition
    (K : Submodule ℝ (B → ℝ)) (w : B → ℕ) (n : ℕ)
    (D : MvPolynomial (U ⊕ B) ℝ)
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) n)
    (A : B → MvPolynomial U ℝ) (hA : ∀ j, (A j).totalDegree ≤ w j)
    (S : MvPolynomial (U ⊕ B) ℝ) (R : MvPolynomial (U ⊕ B) ℚ)
    (q : ℕ) (hq : 0 < q) (r : U → ℤ)
    (H T : U → ℝ) (hH : ∀ i, 0 < H i) (hT : ∀ i, 0 < T i)
    (hsource : ∀ (v : U → ℝ) (b : B → ℝ), b ∈ K →
      eval (Sum.elim v b)
        (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) n
          (jointResidueAffinePolynomial q r D)) =
      eval (Sum.elim (fun i => v i / T i)
        (fun j => b j - eval v
          (majorTranslationTopCoordinates w (fun j => residueAffinePolynomial q r (A j)) j))) S +
      eval₂ (algebraMap ℚ ℝ) (Sum.elim v b) R)
    (c C : ℝ) (hc : 1 ≤ c) (hHT : ∀ i, H i ≤ c * (q : ℝ) * T i)
    (d l : ℕ) (hS : S.totalDegree ≤ d) (hR : R.totalDegree ≤ d)
    (hSmass : realPolynomialMass S ≤ C)
    (hRgrid : (fun α => R.coeff α) ∈ denominatorGrid l) :
    ∃ (S' : MvPolynomial (U ⊕ B) ℝ) (R' : MvPolynomial (U ⊕ B) ℚ),
      (∀ (u : U → ℝ) (b : B → ℝ), b ∈ K →
        eval (Sum.elim u b)
          (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) n D) =
          eval (Sum.elim (fun i => u i / H i)
            (fun j => b j - eval u (majorTranslationTopCoordinates w A j))) S' +
          eval₂ (algebraMap ℚ ℝ) (Sum.elim u b) R') ∧
      realPolynomialMass S' ≤ c^d * C ∧ S'.totalDegree ≤ d ∧ R'.totalDegree ≤ d ∧
      (fun α => R'.coeff α) ∈ denominatorGrid (q^d*l) :=
  algebraic_major_dilation_pullback_decomposition K _ _ S R q hq H T hH hT
    (algebraic_major_affine_top_dilation_identity K w n D hD A hA S R q r T hsource)
    c C hc hHT d l hS hR hSmass hRgrid

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

variable {U B : Type*}

theorem algebraic_major_weighted_affine_top_pullback_decomposition
    (K : Submodule ℝ (B → ℝ)) (w : B → ℕ) (hw : ∀ i, 0 < w i) (n : ℕ)
    (D : MvPolynomial (U ⊕ B) ℝ)
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) n)
    (A : B → MvPolynomial U ℝ) (hA : ∀ j, (A j).totalDegree ≤ w j)
    (S : MvPolynomial (U ⊕ B) ℝ) (R : MvPolynomial (U ⊕ B) ℚ)
    (q : ℕ) (hq : 0 < q) (r : U → ℤ)
    (H T : U → ℝ) (hH : ∀ i, 0 < H i) (hT : ∀ i, 0 < T i)
    (hsource : ∀ (v : U → ℝ) (b : B → ℝ), b ∈ K →
      eval (Sum.elim v b)
        (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) n
          (jointResidueAffinePolynomial q r D)) =
      eval (Sum.elim (fun i => v i / T i)
        (fun j => b j - eval v
          (majorTranslationTopCoordinates w (fun j => residueAffinePolynomial q r (A j)) j))) S +
      eval₂ (algebraMap ℚ ℝ) (Sum.elim v b) R)
    (c C : ℝ) (hc : 1 ≤ c) (hHT : ∀ i, H i ≤ c * (q : ℝ) * T i)
    (d l : ℕ)
    (hS : S ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (hR : R ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (hSmass : realPolynomialMass S ≤ C)
    (hRgrid : (fun α => R.coeff α) ∈ denominatorGrid l) :
    ∃ (S' : MvPolynomial (U ⊕ B) ℝ) (R' : MvPolynomial (U ⊕ B) ℚ),
      S' = majorSlowDilationPullback q H T S ∧
      R' = jointRationalPolynomialDilation q R ∧
      (∀ (u : U → ℝ) (b : B → ℝ), b ∈ K →
        eval (Sum.elim u b)
          (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) n D) =
          eval (Sum.elim (fun i => u i / H i)
            (fun j => b j - eval u (majorTranslationTopCoordinates w A j))) S' +
          eval₂ (algebraMap ℚ ℝ) (Sum.elim u b) R') ∧
      realPolynomialMass S' ≤ c^d * C ∧
      S' ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d ∧
      R' ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d ∧
      S'.totalDegree ≤ d ∧ R'.totalDegree ≤ d ∧
      (fun α => R'.coeff α) ∈ denominatorGrid (q^d*l) :=
  algebraic_major_weighted_dilation_pullback_decomposition w hw K _ _ S R q hq H T hH hT
    (algebraic_major_affine_top_dilation_identity K w n D hD A hA S R q r T hsource)
    c C hc hHT d l hS hR hSmass hRgrid

end Erdos3

end

end OAI
