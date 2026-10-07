import OAI.Combinatorics.Progressions.Estimates.MixedRealPoint
import OAI.Combinatorics.Progressions.Estimates.NormalizedCoefficientRemainder

namespace OAI

section

namespace Erdos3

open Module Submodule
open scoped BigOperators

variable {D I J V : Type*} [Fintype D] [Fintype I] [Fintype J] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (o : OrthonormalBasis I ℝ W)

noncomputable def mixedLiftCoefficient (a : (I → J → ℝ) × (Fin n → J → ℤ)) (j : J) :
    EuclideanSpace ℝ D :=
  mixedRealPoint W b o (fun i => a.1 i j, fun i => (a.2 i j : ℝ) / basisAxisScale b i)

omit [Fintype J] in
theorem mixedLiftCoefficient_eq (a : (I → J → ℝ) × (Fin n → J → ℤ)) (j : J) :
    mixedLiftCoefficient W b o a j = normalizedLatticePoint W b
      (orthonormalMixedChart o (mixedArrayRegroup I (Fin n) J a j)) := rfl

theorem mixedPolynomialPoint_sum (e : J → V →₀ ℕ)
    (a : (I → J → ℝ) × (Fin n → J → ℤ)) (x : V → ℝ) :
    mixedPolynomialPoint W b o e a.1 a.2 x =
      ∑ j, monomialScale x (e j) • mixedLiftCoefficient W b o a j := by
  change mixedRealPoint W b o
    (fun i => MvPolynomial.eval x (monomialArrayPolynomial e (a.1 i)),
      fun i => MvPolynomial.eval x (monomialArrayPolynomial e (fun j => (a.2 i j : ℝ) / basisAxisScale b i))) = _
  simp only [mixedLiftCoefficient, ← map_smul, ← map_sum]
  congr 1
  ext i <;> simp [monomialArrayPolynomial_eval, monomialScale, Finsupp.prod,
    Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, mul_comm]

noncomputable def mixedLiftPolynomial (e : J → V →₀ ℕ)
    (a : (I → J → ℝ) × (Fin n → J → ℤ)) (d : D) : MvPolynomial V ℝ :=
  monomialArrayPolynomial e (fun j => mixedLiftCoefficient W b o a j d)

theorem mixedLiftPolynomial_eval (e : J → V →₀ ℕ)
    (a : (I → J → ℝ) × (Fin n → J → ℤ)) (x : V → ℝ) (d : D) :
    MvPolynomial.eval x (mixedLiftPolynomial W b o e a d) = mixedPolynomialPoint W b o e a.1 a.2 x d := by
  change _ = (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : D => ℝ) d) (mixedPolynomialPoint W b o e a.1 a.2 x)
  rw [mixedPolynomialPoint_sum, map_sum]
  simp [mixedLiftPolynomial, monomialArrayPolynomial_eval, monomialScale, Finsupp.prod, mul_comm]

theorem mixedLiftPolynomial_degree (e : J → V →₀ ℕ)
    (a : (I → J → ℝ) × (Fin n → J → ℤ)) {h : ℕ}
    (he : ∀ j, (e j).sum (fun _ k => k) ≤ h) (d : D) :
    (mixedLiftPolynomial W b o e a d).totalDegree ≤ h := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j _
  exact (MvPolynomial.totalDegree_monomial_le _ _).trans (he j)

theorem mixedLiftPolynomial_coeff (e : J → V →₀ ℕ) (he : Function.Injective e)
    (a : (I → J → ℝ) × (Fin n → J → ℤ)) (d : D) (j : J) :
    (mixedLiftPolynomial W b o e a d).coeff (e j) = mixedLiftCoefficient W b o a j d :=
  monomialArrayPolynomial_coeff e he _ j

theorem mixedLiftPolynomial_coefficient_bound (e : J → V →₀ ℕ) (he : Function.Injective e)
    (a : (I → J → ℝ) × (Fin n → J → ℤ)) (T : V → ℝ) (hT : ∀ v, 0 < T v)
    {M : ℝ} (hM : 0 ≤ M)
    (hbnd : ∀ j d, |mixedLiftCoefficient W b o a j d| ≤ M / monomialScale T (e j))
    (α : V →₀ ℕ) (d : D) :
    |(mixedLiftPolynomial W b o e a d).coeff α| ≤ M / monomialScale T α := by
  classical
  by_cases hα : ∃ j, e j = α
  · obtain ⟨j, rfl⟩ := hα
    rw [mixedLiftPolynomial_coeff W b o e he]
    exact hbnd j d
  · rw [mixedLiftPolynomial, monomialArrayPolynomial_coeff_zero_of_not_mem e _ α
      (fun j hj => hα ⟨j, hj⟩), abs_zero]
    exact div_nonneg hM (monomialScale_pos T hT α).le

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule

variable {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

noncomputable def coefficientRowPolynomial (c : CoefficientArray (K := K) U) (j : Fin m) (i : J j) :
    MvPolynomial K ℝ :=
  monomialArrayPolynomial Subtype.val (fun d : BoundedCoefficientExponent K (j.val + 1) => (c ⟨j, d⟩).val i)

theorem canonicalCoefficientSample_polynomial_remainder
    (a : CoefficientSamplerArrays (K := K) I n) (c : CoefficientArray (K := K) U)
    (hc : canonicalCoefficientSample U b hb o a = QuotientAddGroup.mk' (coefficientIntegerLattice U) c) :
    ∃ β : ∀ j, J j → MvPolynomial K ℤ, ∀ j i,
      coefficientRowPolynomial U c j i =
        mixedLiftPolynomial (euclideanSubspace (U j)) (b j) (o j) Subtype.val (a j) i +
          MvPolynomial.map (Int.castRingHom ℝ) (β j i) ∧ (β j i).totalDegree ≤ j.val + 1 := by
  have hd (j : Fin m) (d : BoundedCoefficientExponent K (j.val + 1)) (i : J j) :
      ∃ z : ℤ, (c ⟨j, d⟩).val i - mixedLiftCoefficient (euclideanSubspace (U j)) (b j) (o j) (a j) d i = z := by
    rw [mixedLiftCoefficient_eq]
    exact canonicalCoefficientSample_integer_remainder U b hb o a c hc j d i
  have hj (j : Fin m) := exists_integerPolynomial_remainder Subtype.val
    (fun d : BoundedCoefficientExponent K (j.val + 1) => (c ⟨j, d⟩).val)
    (fun d i => mixedLiftCoefficient (euclideanSubspace (U j)) (b j) (o j) (a j) d i)
    (fun d => d.property) (hd j)
  choose β hβ using hj
  exact ⟨β, hβ⟩

theorem canonicalCoefficientSample_integer_evaluation
    (a : CoefficientSamplerArrays (K := K) I n) (c : CoefficientArray (K := K) U)
    (hc : canonicalCoefficientSample U b hb o a = QuotientAddGroup.mk' (coefficientIntegerLattice U) c) :
    ∃ β : ∀ j, J j → MvPolynomial K ℤ, (∀ j i, (β j i).totalDegree ≤ j.val + 1) ∧
      ∀ j i (x : K → ℤ), MvPolynomial.eval (fun v => (x v : ℝ)) (coefficientRowPolynomial U c j i) =
        mixedPolynomialPoint (euclideanSubspace (U j)) (b j) (o j) Subtype.val
          (a j).1 (a j).2 (fun v => (x v : ℝ)) i + (MvPolynomial.eval x (β j i) : ℝ) := by
  obtain ⟨β, hβ⟩ := canonicalCoefficientSample_polynomial_remainder U b hb o a c hc
  refine ⟨β, fun j i => (hβ j i).2, ?_⟩
  intro j i x
  have h := integerPolynomial_remainder_eval _ _ (β j i) (hβ j i).1 x
  rwa [mixedLiftPolynomial_eval] at h

end Erdos3.VectorPolynomial

end

end OAI
