import OAI.Combinatorics.Progressions.Polynomial.ExtendedPolynomialValues

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {X R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

theorem coefficients_translate_mem (U : Submodule R V) (a : X → R)
    (p : VectorPolynomial X R V) (hp : ∀ d, coefficients p d ∈ U) (d : X →₀ ℕ) :
    coefficients (translate a p) d ∈ U := by
  rw [coefficients_translate]
  exact Submodule.sum_mem U (fun b _ => U.smul_mem _ (hp b))

theorem coefficients_translate_sub_eq_zero_of_degreeLE
    (w : X → ℕ) (hw : ∀ i, 0 < w i) (a : X → R) {n : ℕ}
    (p : VectorPolynomial X R V) (hp : DegreeLE w n p)
    (d : X →₀ ℕ) (hd : n ≤ Finsupp.weight w d) :
    coefficients (translate a p - p) d = 0 := by
  classical
  rw [coefficients_translate_sub]
  apply Finset.sum_eq_zero
  intro b hb
  have hbdeg := (degreeLE_iff w n p).mp hp b hb
  have hc : (polynomialTranslate a (MvPolynomial.monomial b 1) -
      MvPolynomial.monomial b 1).coeff d = 0 := by
    by_contra hne
    have hlt := (polynomialTranslate_monomial_bounds a w hw b).2
      (MvPolynomial.mem_support_iff.mpr hne)
    exact (not_lt_of_ge (hbdeg.trans hd)) hlt
  rw [hc, zero_smul]

theorem degreeLE_translate (w : X → ℕ) (hw : ∀ i, 0 < w i) (a : X → R) {n : ℕ}
    (p : VectorPolynomial X R V) (hp : DegreeLE w n p) :
    DegreeLE w n (translate a p) := by
  intro d hd
  have h := coefficients_translate_sub_eq_zero_of_degreeLE w hw a p hp d hd.le
  simpa only [map_sub, Finsupp.sub_apply, hp d hd, sub_zero] using h

theorem homogeneousPart_translate (a : X → R) {n : ℕ}
    (p : VectorPolynomial X R V) (hp : DegreeLE (1 : X → ℕ) n p) :
    homogeneousPart n (translate a p) = homogeneousPart n p := by
  classical
  apply coefficients.injective
  ext d
  simp only [coefficients_homogeneousPart]
  split
  · rename_i hd
    have hdw : n ≤ Finsupp.weight (1 : X → ℕ) d := by
      simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hd.ge
    have h := coefficients_translate_sub_eq_zero_of_degreeLE (1 : X → ℕ)
      (fun _ => by norm_num) a p hp d hdw
    simpa only [map_sub, Finsupp.sub_apply, sub_eq_zero] using h
  · rfl

end Erdos3.VectorPolynomial

end

end OAI
