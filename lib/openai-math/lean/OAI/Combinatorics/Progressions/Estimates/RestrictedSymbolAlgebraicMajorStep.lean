/- Modified for ProveIt: adapt import paths to Mathlib v4.32.0.
Mathematical statements and proofs unchanged. -/
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.StdBasis
import OAI.Combinatorics.Progressions.Estimates.RealSymbolGradeQuotientSplitting

namespace OAI

section

namespace Erdos3

open Module
open scoped BigOperators

theorem BasisGradedSubmodule.coordinate_dilation_mem
    {R B : Type*} [Field R] [Fintype B]
    (w : B → ℕ) (K : Submodule R (B → R))
    (hK : BasisGradedSubmodule (Pi.basisFun R B) w K)
    (r : R) (x : B → R) (hx : x ∈ K) :
    (fun i => r ^ w i * x i) ∈ K := by
  classical
  have hprojection (j : ℕ) (i : B) :
      basisGradeProjection (Pi.basisFun R B) w j x i =
        if w i = j then x i else 0 := by
    simpa only [Pi.basisFun_repr] using
      basisGradeProjection_repr (Pi.basisFun R B) w j x i
  have hdilation : (fun i => r ^ w i * x i) =
      ∑ j ∈ Finset.univ.image w, r ^ j • basisGradeProjection (Pi.basisFun R B) w j x := by
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hprojection,
      mul_ite, mul_zero]
    simp
  rw [hdilation]
  exact K.sum_mem (fun j _ => K.smul_mem (r ^ j) (hK j x hx))

def gradedBaseIntersection {U B κ : Type*}
    (K₀ : Set (U ⊕ B → ℝ)) (K : κ → Submodule ℝ (B → ℝ)) :
    Set (U ⊕ B → ℝ) :=
  {t | t ∈ K₀ ∧ ∀ j, (fun b => t (Sum.inr b)) ∈ K j}

theorem gradedBaseIntersection_subset {U B κ : Type*}
    (K₀ : Set (U ⊕ B → ℝ)) (K : κ → Submodule ℝ (B → ℝ)) :
    gradedBaseIntersection K₀ K ⊆ K₀ := fun _ ht => ht.1

theorem gradedBaseIntersection_rat_dilation {U B κ : Type*} [Fintype B]
    (w : B → ℕ) (K₀ : Set (U ⊕ B → ℝ))
    (K : κ → Submodule ℝ (B → ℝ))
    (hK : ∀ j, BasisGradedSubmodule (Pi.basisFun ℝ B) w (K j))
    (hK₀ : ∀ t ∈ K₀, ∀ r : ℚ,
      (fun i => (r : ℝ) ^ Sum.elim (fun _ : U => 1) w i * t i) ∈ K₀)
    (t : U ⊕ B → ℝ) (ht : t ∈ gradedBaseIntersection K₀ K) (r : ℚ) :
    (fun i => (r : ℝ) ^ Sum.elim (fun _ : U => 1) w i * t i) ∈
      gradedBaseIntersection K₀ K := by
  refine ⟨hK₀ t ht.1 r, ?_⟩
  intro j
  exact (hK j).coordinate_dilation_mem w (K j) (r : ℝ)
    (fun b => t (Sum.inr b)) (ht.2 j)

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct Classical

variable {X B J ι L : Type*} [Fintype B] [Fintype J]
  [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : B → ℕ)

theorem exists_restricted_symbol_algebraic_major_grade_step
    (U : Submodule ℚ F.AssociatedGraded)
    (hU : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω U)
    (lift : (F.AssociatedGraded ⧸ U) →ₗ[ℚ] F.AssociatedGraded)
    (hsection : ∀ y, U.mkQ (lift y) = y)
    (basis : Basis J ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U)))
    (k : ℕ) (Z left right : F.RealPolynomialSymbolGroup (Sum.elim (fun _ : X => 1) w))
    (K₀ : Set (X ⊕ B → ℝ)) (K : J → Submodule ℝ (B → ℝ))
    (hK : ∀ j, BasisGradedSubmodule (Pi.basisFun ℝ B) w (K j))
    (hK₀ : ∀ t ∈ K₀, ∀ r : ℚ,
      (fun i => (r : ℝ) ^ Sum.elim (fun _ : X => 1) w i * t i) ∈ K₀)
    (hlower : ∀ t ∈ K₀, ∀ j < k,
      F.realSymbolGradeEvaluation b ω hF (Sum.elim (fun _ : X => 1) w) j t
        (left⁻¹ * Z * right⁻¹).coord ∈ U.baseChange ℝ)
    (D₀ : J → MvPolynomial B ℝ) (A : B → MvPolynomial X ℝ)
    (E : J → MvPolynomial (X ⊕ B) ℝ) (e : J → B → MvPolynomial X ℝ)
    (Q : J → MvPolynomial (X ⊕ B) ℚ) (a : J → B → MvPolynomial X ℚ)
    (potential : J → MvPolynomial B ℚ) (H : X → ℝ)
    (middle : J → (X → ℝ) → PolynomialTranslationGroupOver ℝ B)
    (hfactor : ∀ j u,
      algebraicMajorSymbol (coordinate (basis.coord j).toAddMonoidHom
        (F.realSymbolGradeQuotientPolynomial b ω hF (Sum.elim (fun _ : X => 1) w) U k
          (left⁻¹ * Z * right⁻¹).coord)) (D₀ j) A u =
        normalizedMajorLeft (E j) (e j) H u * middle j u * rationalMajorRight (Q j) (a j) u)
    (hpotential : ∀ j u z, z ∈ K j →
      MvPolynomial.eval z (middle j u).polynomial =
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) z (potential j) -
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (z - (middle j u).base) (potential j))
    (hright : ∀ j u, (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) u (a j x)) ∈ K j)
    (q d : ℕ) (M : ℝ) (hM : 0 ≤ M)
    (he : ∀ j x, realPolynomialMass (e j x) ≤ M)
    (hE : ∀ j, (E j).totalDegree ≤ d) (hV : ∀ j, (potential j).totalDegree ≤ d)
    (hQgrid : ∀ j, (fun α => (Q j).coeff α) ∈ denominatorGrid q)
    (hVgrid : ∀ j, (fun α => (potential j).coeff α) ∈ denominatorGrid q)
    (hagrid : ∀ j x, (fun α => (a j x).coeff α) ∈ denominatorGrid q) :
    ∃ slow rat : VectorPolynomial (X ⊕ B) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U)),
      (∀ α j, |basis.repr (coefficients slow α) j| ≤ realPolynomialMass (D₀ j) +
        (realPolynomialMass (E j) +
          realPolynomialMass (MvPolynomial.map (algebraMap ℚ ℝ) (potential j))) * (1 + M)^d) ∧
      (∀ α, (fun j => basis.repr (coefficients rat α) j) ∈ realDenominatorGrid (q^(d+1))) ∧
      ∃ Astep Dstep : F.RealPolynomialSymbolGroup (Sum.elim (fun _ : X => 1) w),
        Astep.coord = F.homogeneousQuotientSymbolLift b ω hF (Sum.elim (fun _ : X => 1) w)
          k (lift.baseChange ℝ) (weightedHomogeneousPart (Sum.elim (fun _ : X => 1) w) k
            (realChartSubstitute (normalizedRealPolynomialChart H A) slow)) ∧
        Dstep.coord = F.homogeneousQuotientSymbolLift b ω hF (Sum.elim (fun _ : X => 1) w)
          k (lift.baseChange ℝ) (weightedHomogeneousPart (Sum.elim (fun _ : X => 1) w) k rat) ∧
        Astep.coord ∈ (F.polynomialSymbolFiltration (Sum.elim (fun _ : X => 1) w)).realification.layer k ∧
        Dstep.coord ∈ (F.polynomialSymbolFiltration (Sum.elim (fun _ : X => 1) w)).realification.layer k ∧
        (left * Astep) * ((left * Astep)⁻¹ * Z * (Dstep * right)⁻¹) * (Dstep * right) = Z ∧
        (∀ t, ∀ j < k,
          F.realSymbolGradeEvaluation b ω hF (Sum.elim (fun _ : X => 1) w) j t
            ((left * Astep)⁻¹ * Z * (Dstep * right)⁻¹).coord =
          F.realSymbolGradeEvaluation b ω hF (Sum.elim (fun _ : X => 1) w) j t
            (left⁻¹ * Z * right⁻¹).coord) ∧
        ∀ t ∈ gradedBaseIntersection K₀ K, ∀ j ≤ k,
          F.realSymbolGradeEvaluation b ω hF (Sum.elim (fun _ : X => 1) w) j t
            ((left * Astep)⁻¹ * Z * (Dstep * right)⁻¹).coord ∈ U.baseChange ℝ := by
  obtain ⟨slow, rat, hidentity, hslow, hrat⟩ := exists_vector_algebraic_major_decomposition basis
    (F.realSymbolGradeQuotientPolynomial b ω hF (Sum.elim (fun _ : X => 1) w) U k
      (left⁻¹ * Z * right⁻¹).coord)
    K D₀ A E e Q a potential H middle hfactor hpotential hright q d M hM he hE hV
    hQgrid hVgrid hagrid
  have hquot : ∀ t ∈ gradedBaseIntersection K₀ K,
      U.mkQ.baseChange ℝ
        (F.realSymbolGradeEvaluation b ω hF (Sum.elim (fun _ : X => 1) w) k t
          (left⁻¹ * Z * right⁻¹).coord) =
        eval₂ t (realChartSubstitute (normalizedRealPolynomialChart H A) slow) + eval₂ t rat := by
    intro t ht
    have h := hidentity (fun i => t (Sum.inl i)) (fun i => t (Sum.inr i)) ht.2
    have hsplit : Sum.elim (fun i => t (Sum.inl i)) (fun i => t (Sum.inr i)) = t := by
      funext i
      cases i <;> rfl
    rw [hsplit, F.realSymbolGradeQuotientPolynomial_eval] at h
    with_reducible exact h
  have hstep := F.restricted_symbol_major_grade_step b ω hF (Sum.elim (fun _ : X => 1) w)
    U hU lift hsection k Z left right K₀ (gradedBaseIntersection K₀ K)
    (gradedBaseIntersection_subset K₀ K)
    (gradedBaseIntersection_rat_dilation w K₀ K hK hK₀)
    (realChartSubstitute (normalizedRealPolynomialChart H A) slow) rat hlower hquot
  with_reducible exact ⟨slow, rat, hslow, hrat, hstep⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
