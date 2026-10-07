import OAI.Combinatorics.Progressions.Polynomial.BoundedArrayPolynomial

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

def boundedSiteMatrix {K S : Type*} (h : ℕ) (site : S → K → ℤ) :
    Matrix S (BoundedCoefficientExponent K h) ℤ :=
  fun s d => d.val.prod (fun k n => site s k ^ n)

theorem siteEvaluation_boundedArrayPolynomial {K S W : Type*} [Fintype K]
    [AddCommGroup W] [Module ℝ W] (h : ℕ) (site : S → K → ℤ)
    (x : BoundedCoefficientExponent K h → W) :
    siteEvaluation (fun s k => (site s k : ℝ)) (boundedArrayPolynomial h x) =
      matrixModuleAction (fun s d => (boundedSiteMatrix h site s d : ℝ)) x := by
  funext s
  change eval (fun k => (site s k : ℝ)) (boundedArrayPolynomial h x) =
    ∑ d : BoundedCoefficientExponent K h, (boundedSiteMatrix h site s d : ℝ) • x d
  simp only [boundedArrayPolynomial, map_sum, eval_monomial,
    boundedSiteMatrix, Finsupp.prod, Int.cast_prod, Int.cast_pow]

theorem siteEvaluation_bounded_coefficients {K S W : Type*} [Fintype K]
    [AddCommGroup W] [Module ℝ W] {h : ℕ} (site : S → K → ℤ)
    (p : VectorPolynomial K ℝ W) (hp : DegreeLE (1 : K → ℕ) h p) :
    siteEvaluation (fun s k => (site s k : ℝ)) p =
      matrixModuleAction (fun s d => (boundedSiteMatrix h site s d : ℝ))
        (fun d => coefficients p d.val) := by
  rw [← boundedArrayPolynomial_reconstruct p hp, siteEvaluation_boundedArrayPolynomial]
  simp only [boundedArrayPolynomial_coeff]

theorem bounded_site_factorization_to_array {K S J : Type*} [Fintype K] [Fintype J]
    (U : Submodule ℝ (J → ℝ)) (h : ℕ) (site : S → K → ℤ)
    (frequency : (K →₀ ℕ) → J → ℝ) (M : (S → U) →ₗ[ℝ] ℝ)
    (hf : ∀ p : VectorPolynomial K ℝ U, DegreeLE (1 : K → ℕ) h p →
      coefficientFunctional frequency (map U.subtype p) = M (siteEvaluation (fun s k => (site s k : ℝ)) p)) :
    ∀ x, subspaceArrayFunctional U (fun d : BoundedCoefficientExponent K h => frequency d.val) x =
      M (matrixModuleAction (fun s d => (boundedSiteMatrix h site s d : ℝ)) x) := by
  intro x
  have he := hf (boundedArrayPolynomial h x) (boundedArrayPolynomial_degreeLE h x)
  rwa [coefficientFunctional_boundedArrayPolynomial, siteEvaluation_boundedArrayPolynomial] at he

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators Matrix

noncomputable def booleanJetExtractionMatrix {α O : Type*} [DecidableEq α]
    (rows : O → Finset α) : Matrix O (Finset α) ℤ :=
  fun o t => if t ⊆ rows o then (-1 : ℤ) ^ (rows o \ t).card else 0

theorem booleanJetExtractionMatrix_mulVec {α O : Type*} [Fintype α] [DecidableEq α]
    (rows : O → Finset α) (f : Finset α → ℤ) (o : O) :
    (booleanJetExtractionMatrix rows *ᵥ f) o = booleanCoefficient f (rows o) := by
  classical
  change (∑ t, (if t ⊆ rows o then (-1 : ℤ) ^ (rows o \ t).card else 0) * f t) = _
  simp only [ite_mul, zero_mul, ← Finset.sum_filter]
  have hsets : Finset.univ.filter (fun t : Finset α => t ⊆ rows o) = (rows o).powerset := by
    ext t
    simp
  rw [hsets]
  rfl

def boundedCoefficientIntegerExponentEquiv (K : Type*) (h : ℕ) :
    VectorPolynomial.BoundedCoefficientExponent K h ≃ BoundedIntegerExponent K h where
  toFun e := ⟨e.val, e.property⟩
  invFun e := ⟨e.val, e.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def boundedCoefficientJetMatrix {α K O : Type*} [DecidableEq α] [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (h : ℕ) (rows : O → Finset α) :
    Matrix O (VectorPolynomial.BoundedCoefficientExponent K h) ℤ :=
  fun o e => boundedDegreeIntegerJetMatrix root D h rows o
    (boundedCoefficientIntegerExponentEquiv K h e)

theorem booleanJetExtractionMatrix_mul_boundedSite {α K O : Type*}
    [Fintype α] [DecidableEq α] [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (h : ℕ) (rows : O → Finset α) :
    booleanJetExtractionMatrix rows *
        VectorPolynomial.boundedSiteMatrix h (integerAffineCube root D) =
      boundedCoefficientJetMatrix root D h rows := by
  ext o e
  change (booleanJetExtractionMatrix rows *ᵥ
    (fun t => VectorPolynomial.boundedSiteMatrix h (integerAffineCube root D) t e)) o = _
  rw [booleanJetExtractionMatrix_mulVec]
  change booleanCoefficient _ (rows o) = booleanCoefficient _ (rows o)
  congr 1
  funext t
  simp [VectorPolynomial.boundedSiteMatrix, MvPolynomial.eval_monomial, Finsupp.prod,
    boundedCoefficientIntegerExponentEquiv]

theorem boundedCoefficientJetMatrix_period {α K O : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] [Fintype O]
    (root : K → ℤ) (D : Matrix α K ℤ) (a : ℤ)
    (hperiod : integerScalarLattice α a ≤ D.mulVecLin.range)
    (h : ℕ) (rows : O → Finset α) (hinj : Function.Injective rows)
    (hdegree : ∀ o, (rows o).card ≤ h) :
    integerScalarLattice O (a ^ h) ≤ (boundedCoefficientJetMatrix root D h rows).mulVecLin.range := by
  intro y hy
  obtain ⟨x, hx⟩ := boundedDegreeIntegerJetMatrix_period root D a hperiod h rows hinj hdegree hy
  let e := boundedCoefficientIntegerExponentEquiv K h
  refine ⟨fun d => x (e d), ?_⟩
  ext o
  change (∑ d, boundedCoefficientJetMatrix root D h rows o d * x (e d)) = y o
  calc
    _ = ∑ d, boundedDegreeIntegerJetMatrix root D h rows o d * x d :=
      Fintype.sum_equiv e _ _ (fun _ => rfl)
    _ = y o := congrFun hx o

end Erdos3

end

end OAI
