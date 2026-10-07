import OAI.Combinatorics.Progressions.Lattices.AffineCoefficientResidueWidths

namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem degreeLE_monomial_of_degree_le {K W : Type*} [AddCommGroup W] [Module ℝ W]
    {d : K →₀ ℕ} {h : ℕ} (hd : d.degree ≤ h) (w : W) :
    DegreeLE (1 : K → ℕ) h (monomial (R := ℝ) d w) := by
  classical
  intro e he
  rw [coefficients_monomial]
  by_cases hed : e = d
  · subst e
    have hh : h < d.degree := by simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using he
    exact False.elim ((not_lt_of_ge hd) hh)
  · simp [Ne.symm hed]

theorem affineModeLift_zero_iff_bounded {K W : Type*} [AddCommGroup W] [Module ℝ W]
    (L : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ) (h : ℕ) :
    (∀ P, Homogeneous h P → affineModeLift L P = 0) ↔
      ∀ P, DegreeLE (1 : K → ℕ) h P → L P = 0 := by
  simpa only [affineModeLift, LinearMap.comp_apply, LinearMap.zero_apply] using
    homogeneous_site_factorization_iff h (Empty.elim : Empty → K → ℝ) L
      (0 : (Empty → W) →ₗ[ℝ] ℝ)

theorem coefficientArrayFunctional_eq_zero_iff_trivial {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ) :
    coefficientArrayFunctional U frequency = 0 ↔ affineCoefficientModeTrivial U frequency := by
  rw [coefficientArrayFunctional_eq_zero_iff]
  constructor
  · intro hz j P hP
    by_contra hn
    have hn' : coefficientFunctional
        (fun d a => ((affineLiftFrequency (frequency j) d a : ℤ) : ℝ)) (map (U j).subtype P) ≠ 0 := by
      rwa [← affineModeLift_integerFrequency]
    obtain ⟨d, hd, w, hw⟩ := exists_restricted_coefficient_nonzero (U j)
      (affineLiftFrequency (frequency j)) ⟨P, hP, hn'⟩
    exact hw (hz ⟨j, ⟨d.some, (some_degree_le d).trans hd.le⟩⟩ w)
  · intro hz s w
    let L := (coefficientFunctional (fun d a => (frequency s.1 d a : ℝ))).comp (map (U s.1).subtype)
    have hlift : ∀ P, Homogeneous (s.1.val + 1) P → affineModeLift L P = 0 := by
      simpa only [L, affineModeLift_comp_map, LinearMap.comp_apply] using hz s.1
    have he := (affineModeLift_zero_iff_bounded L (s.1.val + 1)).mp hlift
      (monomial s.2.val w) (degreeLE_monomial_of_degree_le s.2.property w)
    simpa only [L, LinearMap.comp_apply, map_monomial, Submodule.subtype_apply,
      coefficientFunctional_monomial] using he

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

theorem sum_bounded_monomial_coefficients {K W : Type*} [Fintype K]
    [AddCommGroup W] [Module ℝ W] {h : ℕ}
    (p : VectorPolynomial K ℝ W) (hp : DegreeLE (1 : K → ℕ) h p) :
    (∑ d : BoundedCoefficientExponent K h, monomial d.val (coefficients p d.val)) = p := by
  apply coefficients.injective
  ext e
  simp only [map_sum, Finsupp.finsetSum_apply, coefficients_monomial]
  by_cases he : e.degree ≤ h
  · rw [Finset.sum_eq_single (⟨e, he⟩ : BoundedCoefficientExponent K h)]
    · simp
    · intro d _ hd
      have hde : d.val ≠ e := fun h => hd (Subtype.ext h)
      simp [hde]
    · simp
  · have hz : coefficients p e = 0 := hp e (by
      simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using lt_of_not_ge he)
    rw [hz]
    apply Finset.sum_eq_zero
    intro d _
    have hde : d.val ≠ e := fun h => he (h ▸ d.property)
    simp [hde]

theorem coefficientFunctional_bounded_expansion {K J : Type*} [Fintype K] [Fintype J]
    (frequency : (K →₀ ℕ) → J → ℝ) {h : ℕ}
    (p : VectorPolynomial K ℝ (J → ℝ)) (hp : DegreeLE (1 : K → ℕ) h p) :
    coefficientFunctional frequency p =
      ∑ d : BoundedCoefficientExponent K h, ∑ a, frequency d.val a * coefficients p d.val a := by
  conv_lhs => rw [← sum_bounded_monomial_coefficients p hp]
  simp only [map_sum, coefficientFunctional_monomial]

end Erdos3.VectorPolynomial

end

end OAI
