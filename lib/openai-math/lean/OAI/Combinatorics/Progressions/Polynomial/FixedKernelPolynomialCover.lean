import OAI.Combinatorics.Progressions.Estimates.BoundedExtendedSiteSection
import OAI.Combinatorics.Progressions.Estimates.BoundedHomogeneousFactorization
import OAI.Combinatorics.Progressions.Linear.FixedKernelSiteImage

namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem exists_polynomial_site_cover :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {K S : Type*} [Fintype K] [Fintype S]
    (h : ℕ) (site : S → K → ℤ) {H : ℕ} (_hH : 1 ≤ H)
    (_hE : ∀ s d, RationalHeightLE (boundedSiteMatrix h site s d : ℚ) H)
    {P : ℝ} (_hP : 0 ≤ P) (_hD : (Fintype.card (BoundedCoefficientExponent K h) : ℝ) ≤ P)
    (_hS : (Fintype.card S : ℝ) ≤ P) (_hHP : (H : ℝ) ≤ Real.exp P),
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ Real.exp ((P + A) ^ A) ∧
    ∀ {J : Type*} [Fintype J] (U : Submodule ℝ (J → ℝ)) (frequency : (K →₀ ℕ) → J → ℤ)
    {C : ℝ} (_hC : 0 ≤ C) (_hCP : C ≤ Real.exp P)
    (_hfrequency : ∀ d, d.degree ≤ h → ∀ a, |(frequency d a : ℝ)| ≤ C)
    (M : (S → U) →ₗ[ℝ] ℝ)
    (_hfactor : ∀ p : VectorPolynomial K ℝ U, DegreeLE (1 : K → ℕ) h p →
      coefficientFunctional (fun d a => (frequency d a : ℝ)) (map U.subtype p) =
        M (siteEvaluation (fun s k => (site s k : ℝ)) p)),
    ∃ b : Matrix S J ℤ, (∀ s a, |(b s a : ℝ)| ≤ Real.exp ((P + A) ^ A)) ∧
      ∀ p : VectorPolynomial K ℝ U, DegreeLE (1 : K → ℕ) h p →
        CircleFourier.character
          (coefficientFunctional (fun d a => (frequency d a : ℝ)) (map U.subtype p) : CircleFourier.Circle) =
        subspaceArrayCharacter U b (QuotientAddGroup.mk' (subspaceArrayIntegerLattice S U)
          ((q : ℝ)⁻¹ • siteEvaluation (fun s k => (site s k : ℝ)) p)) := by
  classical
  obtain ⟨A, hA, hdenominator⟩ := exists_common_site_denominator
  refine ⟨A, hA, ?_⟩
  intro K S _ _ h site H hH hE P hP hD hS hHP
  obtain ⟨q, hq, hqP, hrows⟩ := hdenominator
    (fun s d => (boundedSiteMatrix h site s d : ℚ)) hH hE hP hD hS hHP
  refine ⟨q, hq, hqP, ?_⟩
  intro J _ U frequency C hC hCP hfrequency M hfactor
  obtain ⟨b, hb, he⟩ := hrows U (fun d a => frequency d.val a) hC hCP
    (fun d a => hfrequency d.val d.property a) M
    (fun x => by
      simpa only [Rat.cast_intCast] using bounded_site_factorization_to_array U h site
        (fun d a => (frequency d a : ℝ)) M hfactor x)
  refine ⟨b, hb, ?_⟩
  intro p hp
  have hfun := coefficientFunctional_boundedArrayPolynomial U h
    (fun d a => (frequency d a : ℝ)) (fun d => coefficients p d.val)
  rw [boundedArrayPolynomial_reconstruct p hp] at hfun
  have hrow := he (fun d => coefficients p d.val)
  simp only [Rat.cast_intCast, map_smul] at hrow
  rw [← siteEvaluation_bounded_coefficients site p hp] at hrow
  rw [subspaceArrayCharacter_mk, map_smul]
  exact congrArg (fun r : ℝ => CircleFourier.character (r : CircleFourier.Circle)) (hfun.trans hrow)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix

noncomputable def boundedExponentMap {K I : Type*} (e : K → I) (h : ℕ)
    (d : BoundedCoefficientExponent K h) : BoundedCoefficientExponent I h :=
  ⟨d.val.mapDomain e, by rw [Finsupp.degree_mapDomain]; exact d.property⟩

theorem boundedSiteMatrix_mapDomain {K I S : Type*} (h : ℕ) (site : S → I → ℤ) (e : K → I) :
    (boundedSiteMatrix h site).submatrix id (boundedExponentMap e h) =
      boundedSiteMatrix h (fun s k => site s (e k)) := by
  ext s d
  change (d.val.mapDomain e).prod (fun i n => site s i ^ n) = d.val.prod (fun k n => site s (e k) ^ n)
  exact Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)

theorem exists_fixed_kernel_polynomial_cover :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {K α : Type*} [Fintype K] [Fintype α] [DecidableEq α]
    (root₀ : K → ℤ) (D₀ : Matrix α K ℤ) (a : ℤ) (_ha : a ≠ 0)
    (_hperiod : integerScalarLattice α a ≤ D₀.mulVecLin.range)
    (h : ℕ) {H : ℕ} (_hH : 1 ≤ H)
    (_hE : ∀ s d, RationalHeightLE (boundedSiteMatrix h (integerAffineCube root₀ D₀) s d : ℚ) H)
    {P : ℝ} (_hP : 0 ≤ P) (_hK : (Fintype.card (BoundedCoefficientExponent K h) : ℝ) ≤ P)
    (_hS : (Fintype.card (Finset α) : ℝ) ≤ P) (_hHP : (H : ℝ) ≤ Real.exp P),
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ Real.exp ((P + A) ^ A) ∧
    ∀ {I J : Type*} [Fintype I] [Fintype J]
    (root : I → ℤ) (D : Matrix α I ℤ) (e : K → I)
    (_hroot : ∀ k, root (e k) = root₀ k) (_hD : ∀ i k, D i (e k) = D₀ i k)
    (U : Submodule ℝ (J → ℝ)) (frequency : (I →₀ ℕ) → J → ℤ)
    {C : ℝ} (_hC : 0 ≤ C) (_hCP : C ≤ Real.exp P)
    (_hfrequency : ∀ d, d.degree ≤ h → ∀ j, |(frequency d j : ℝ)| ≤ C)
    (M : (Finset α → U) →ₗ[ℝ] ℝ)
    (_hfactor : ∀ p : VectorPolynomial I ℝ U, DegreeLE (1 : I → ℕ) h p →
      coefficientFunctional (fun d j => (frequency d j : ℝ)) (map U.subtype p) =
        M (siteEvaluation (fun s i => (integerAffineCube root D s i : ℝ)) p)),
    ∃ b : Matrix (Finset α) J ℤ, (∀ s j, |(b s j : ℝ)| ≤ Real.exp ((P + A) ^ A)) ∧
      ∀ p : VectorPolynomial I ℝ U, DegreeLE (1 : I → ℕ) h p →
        CircleFourier.character
          (coefficientFunctional (fun d j => (frequency d j : ℝ)) (map U.subtype p) : CircleFourier.Circle) =
        subspaceArrayCharacter U b (QuotientAddGroup.mk' (subspaceArrayIntegerLattice (Finset α) U)
          ((q : ℝ)⁻¹ • siteEvaluation (fun s i => (integerAffineCube root D s i : ℝ)) p)) := by
  classical
  obtain ⟨A, hA, hcover⟩ := exists_common_site_denominator_from_columns
  refine ⟨A, hA, ?_⟩
  intro K α _ _ _ root₀ D₀ a ha hperiod h H hH hE P hP hK hS hHP
  obtain ⟨q, hq, hqP, hrows⟩ := hcover
    (Matrix.of (fun s d => (boundedSiteMatrix h (integerAffineCube root₀ D₀) s d : ℚ))) hH hE hP hK hS hHP
  refine ⟨q, hq, hqP, ?_⟩
  intro I J _ _ root D e hroot hD U frequency C hC hCP hfrequency M hfactor
  have hsite : (fun s k => integerAffineCube root D s (e k)) = integerAffineCube root₀ D₀ := by
    funext s k
    simp only [integerAffineCube, hroot, hD]
  have hc : (boundedSiteMatrix h (integerAffineCube root D)).submatrix id (boundedExponentMap e h) =
      boundedSiteMatrix h (integerAffineCube root₀ D₀) := by rw [boundedSiteMatrix_mapDomain, hsite]
  have hcq : (Matrix.of (fun s d => (boundedSiteMatrix h (integerAffineCube root D) s d : ℚ))).submatrix
      id (boundedExponentMap e h) =
      Matrix.of (fun s d => (boundedSiteMatrix h (integerAffineCube root₀ D₀) s d : ℚ)) := by
    ext s d
    exact congrArg (fun z : ℤ => (z : ℚ)) (congrFun (congrFun hc s) d)
  obtain ⟨R, hR⟩ := boundedSiteMatrix_fixed_kernel_factor root₀ D₀ a ha hperiod h root D
  obtain ⟨b, hb, he⟩ := hrows
    (Matrix.of (fun s d => (boundedSiteMatrix h (integerAffineCube root D) s d : ℚ)))
    (boundedExponentMap e h) hcq R (by simpa only [Matrix.of_apply, Rat.cast_intCast] using hR)
    U (fun d j => frequency d.val j) hC hCP
    (fun d j => hfrequency _ (boundedExponentMap e h d).property j) M
    (fun x => by
      simpa only [Matrix.of_apply, Rat.cast_intCast] using bounded_site_factorization_to_array U h (integerAffineCube root D)
        (fun d j => (frequency d j : ℝ)) M hfactor x)
  refine ⟨b, hb, ?_⟩
  intro p hp
  have hfun := coefficientFunctional_boundedArrayPolynomial U h
    (fun d j => (frequency d j : ℝ)) (fun d => coefficients p d.val)
  rw [boundedArrayPolynomial_reconstruct p hp] at hfun
  have hrow := he (fun d => coefficients p d.val)
  simp only [Matrix.of_apply, Rat.cast_intCast, map_smul] at hrow
  rw [← siteEvaluation_bounded_coefficients (integerAffineCube root D) p hp] at hrow
  rw [subspaceArrayCharacter_mk, map_smul]
  exact congrArg (fun r : ℝ => CircleFourier.character (r : CircleFourier.Circle)) (hfun.trans hrow)

end Erdos3.VectorPolynomial

end

end OAI
