import OAI.Combinatorics.Progressions.Geometry.MixedCoefficientSmallSupport
import OAI.Combinatorics.Progressions.Polynomial.IntegerPolynomialActiveProfileSupport

namespace OAI

section

namespace Erdos3

open MeasureTheory Module Submodule

variable {D I J V : Type*} [Fintype D] [Fintype I] [Fintype J] {n : ℕ}

noncomputable def mixedPolynomialPoint (W : Submodule ℝ (EuclideanSpace ℝ D))
    (b : Basis (Fin n) ℝ Wᗮ) (o : OrthonormalBasis I ℝ W) (e : J → V →₀ ℕ)
    (a : I → J → ℝ) (z : Fin n → J → ℤ) (x : V → ℝ) : EuclideanSpace ℝ D :=
  (normalizedOrthogonalChart W b).symm
    (orthonormalChart o (fun i => MvPolynomial.eval x (monomialArrayPolynomial e (a i))),
      fun i => MvPolynomial.eval x
        (monomialArrayPolynomial e (fun j => (z i j : ℝ) / basisAxisScale b i)))

theorem mixedPolynomialPoint_small (W : Submodule ℝ (EuclideanSpace ℝ D))
    (b : Basis (Fin n) ℝ Wᗮ) (o : OrthonormalBasis I ℝ W) (e : J → V →₀ ℕ)
    (a : I → J → ℝ) (z : Fin n → J → ℤ) (x : V → ℝ) {C R : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hchart : ∀ p, ‖(normalizedOrthogonalChart W b).symm p‖ ≤ C * ‖p‖)
    (hsmall : C * ((Fintype.card I : ℝ) + 1) * R ≤ 1 / 4)
    (ha : ∀ i, |MvPolynomial.eval x (monomialArrayPolynomial e (a i))| ≤ R)
    (hz : ∀ i, |MvPolynomial.eval x
      (monomialArrayPolynomial e (fun j => (z i j : ℝ) / basisAxisScale b i))| ≤ R) :
    mixedPolynomialPoint W b o e a z x ∈ standardLatticeSmallBox D := by
  let u : I → ℝ := fun i => MvPolynomial.eval x (monomialArrayPolynomial e (a i))
  let v : Fin n → ℝ := fun i => MvPolynomial.eval x
    (monomialArrayPolynomial e (fun j => (z i j : ℝ) / basisAxisScale b i))
  have hu : ‖u‖ ≤ R := (pi_norm_le_iff_of_nonneg hR).mpr (by simpa only [Real.norm_eq_abs] using ha)
  have hv : ‖v‖ ≤ R := (pi_norm_le_iff_of_nonneg hR).mpr (by simpa only [Real.norm_eq_abs] using hz)
  have ho : ‖orthonormalChart o u‖ ≤ (Fintype.card I : ℝ) * R :=
    (orthonormalChart_norm_le o u).trans (mul_le_mul_of_nonneg_left hu (Nat.cast_nonneg _))
  have hp : ‖(orthonormalChart o u, v)‖ ≤ ((Fintype.card I : ℝ) + 1) * R := by
    rw [Prod.norm_def]
    apply max_le <;> nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card I)]
  have hn : ‖mixedPolynomialPoint W b o e a z x‖ ≤ 1 / 4 := by
    apply (hchart (orthonormalChart o u, v)).trans
    exact (mul_le_mul_of_nonneg_left hp hC).trans (by simpa only [mul_assoc] using hsmall)
  intro d
  have hd := PiLp.norm_apply_le (mixedPolynomialPoint W b o e a z x) d
  rw [Real.norm_eq_abs] at hd
  exact (hd.trans hn).trans_lt (by norm_num)

theorem mixedPolynomialPoint_integer (W : Submodule ℝ (EuclideanSpace ℝ D))
    (b : Basis (Fin n) ℝ Wᗮ) (o : OrthonormalBasis I ℝ W) (e : J → V →₀ ℕ)
    (a : I → J → ℝ) (z : Fin n → J → ℤ) (x : V → ℤ) :
    mixedPolynomialPoint W b o e a z (fun v => (x v : ℝ)) =
      normalizedLatticePoint W b (orthonormalMixedChart o
        (fun i => MvPolynomial.eval (fun v => (x v : ℝ)) (monomialArrayPolynomial e (a i)),
          fun i => MvPolynomial.eval x (integerMonomialArrayPolynomial e (z i)))) := by
  unfold mixedPolynomialPoint
  simp_rw [integerMonomialArrayPolynomial_normalized_eval]
  rfl

noncomputable def independentPolynomialLaw (μ : I → Measure (J → ℝ))
    (ν : Fin n → Measure (J → ℤ)) : Measure ((I → J → ℝ) × (Fin n → J → ℤ)) :=
  (Measure.pi μ).prod (Measure.pi ν)

omit [Fintype D] [Fintype J] in
theorem independentPolynomialLaw_probability (μ : I → Measure (J → ℝ))
    (ν : Fin n → Measure (J → ℤ)) [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)] :
    IsProbabilityMeasure (independentPolynomialLaw μ ν) := by
  unfold independentPolynomialLaw
  infer_instance

theorem independentPolynomialLaw_ae_chart (W : Submodule ℝ (EuclideanSpace ℝ D))
    (b : Basis (Fin n) ℝ Wᗮ) (o : OrthonormalBasis I ℝ W) (e : J → V →₀ ℕ) (T : V → ℝ)
    (μ : I → Measure (J → ℝ)) (ν : Fin n → Measure (J → ℤ))
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)]
    {C R : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hchart : ∀ p, ‖(normalizedOrthogonalChart W b).symm p‖ ≤ C * ‖p‖)
    (hsmall : C * ((Fintype.card I : ℝ) + 1) * R ≤ 1 / 4)
    (hμ : ∀ i, ∀ᵐ a ∂μ i, ∀ x : V → ℝ, (∀ v, |x v| ≤ T v) →
      |MvPolynomial.eval x (monomialArrayPolynomial e a)| ≤ R)
    (hν : ∀ i, ∀ᵐ z ∂ν i, ∀ x : V → ℝ, (∀ v, |x v| ≤ T v) →
      |MvPolynomial.eval x (monomialArrayPolynomial e (fun j => (z j : ℝ) / basisAxisScale b i))| ≤ R) :
    ∀ᵐ p ∂independentPolynomialLaw μ ν, ∀ x : V → ℝ, (∀ v, |x v| ≤ T v) →
      mixedPolynomialPoint W b o e p.1 p.2 x ∈ standardLatticeSmallBox D := by
  have hu := finiteProduct_coordinates_ae μ _ hμ
  have hz := finiteProduct_coordinates_ae ν _ hν
  have hu' := (measurePreserving_fst (μ := Measure.pi μ) (ν := Measure.pi ν)).quasiMeasurePreserving.ae hu
  have hz' := (measurePreserving_snd (μ := Measure.pi μ) (ν := Measure.pi ν)).quasiMeasurePreserving.ae hz
  filter_upwards [hu', hz'] with p hp hq
  intro x hx
  exact mixedPolynomialPoint_small W b o e p.1 p.2 x hC hR hchart hsmall
    (fun i => hp i x hx) (fun i => hq i x hx)

end Erdos3

end

end OAI
