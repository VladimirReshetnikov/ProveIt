import OAI.Combinatorics.Progressions.Estimates.BoundedExtendedSiteSection
import OAI.Combinatorics.Progressions.Linear.BooleanJetMatrixFactor

namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

theorem integer_section_functional_factor {I S J : Type*}
    [Fintype I] [Fintype S] [Fintype J]
    (U : Submodule ℝ (J → ℝ)) (E : Matrix S I ℤ) (T : Matrix I S ℤ)
    (d : ℕ) (hd : 0 < d)
    (hT : ∀ x : I → U, matrixModuleAction (fun s i => (E s i : ℝ))
      (matrixModuleAction (fun i s => (T i s : ℝ))
        (matrixModuleAction (fun s i => (E s i : ℝ)) x)) =
        (d : ℝ) • matrixModuleAction (fun s i => (E s i : ℝ)) x)
    (frequency : Matrix I J ℤ) (M : (S → U) →ₗ[ℝ] ℝ)
    (hfactor : ∀ x, subspaceArrayFunctional U (fun i a => (frequency i a : ℝ)) x =
      M (matrixModuleAction (fun s i => (E s i : ℝ)) x)) (x : I → U) :
    subspaceArrayFunctional U (fun i a => (frequency i a : ℝ)) x =
      subspaceArrayFunctional U (fun s a => ((T.transpose * frequency) s a : ℝ))
        ((d : ℝ)⁻¹ • matrixModuleAction (fun s i => (E s i : ℝ)) x) := by
  have hfun : subspaceArrayFunctional U (fun i a => (frequency i a : ℝ))
      (matrixModuleAction (fun i s => (T i s : ℝ))
        (matrixModuleAction (fun s i => (E s i : ℝ)) x)) =
      (d : ℝ) • subspaceArrayFunctional U (fun i a => (frequency i a : ℝ)) x := by
    rw [hfactor, hT, map_smul, hfactor]
  have hcast : Matrix.of (fun s a => ((T.transpose * frequency) s a : ℝ)) =
      (Matrix.of (fun i s => (T i s : ℝ))).transpose * Matrix.of (fun i a => (frequency i a : ℝ)) := by
    ext s a
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Int.cast_sum, Int.cast_mul]
  rw [show (fun s a => ((T.transpose * frequency) s a : ℝ)) =
      ((Matrix.of (fun i s => (T i s : ℝ))).transpose *
        Matrix.of (fun i a => (frequency i a : ℝ))) from hcast]
  rw [← subspaceArrayFunctional_matrix, map_smul, map_smul]
  change subspaceArrayFunctional U (fun i a => (frequency i a : ℝ)) x =
    (d : ℝ)⁻¹ • subspaceArrayFunctional U (fun i a => (frequency i a : ℝ))
      (matrixModuleAction (fun i s => (T i s : ℝ))
        (matrixModuleAction (fun s i => (E s i : ℝ)) x))
  rw [hfun]
  have hn : (d : ℝ) ≠ 0 := (Nat.cast_pos.mpr hd).ne'
  simp only [smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]

theorem integer_section_character_factor {I S J : Type*}
    [Fintype I] [Fintype S] [Fintype J]
    (U : Submodule ℝ (J → ℝ)) (E : Matrix S I ℤ) (T : Matrix I S ℤ)
    (d : ℕ) (hd : 0 < d)
    (hT : ∀ x : I → U, matrixModuleAction (fun s i => (E s i : ℝ))
      (matrixModuleAction (fun i s => (T i s : ℝ))
        (matrixModuleAction (fun s i => (E s i : ℝ)) x)) =
        (d : ℝ) • matrixModuleAction (fun s i => (E s i : ℝ)) x)
    (frequency : Matrix I J ℤ) (M : (S → U) →ₗ[ℝ] ℝ)
    (hfactor : ∀ x, subspaceArrayFunctional U (fun i a => (frequency i a : ℝ)) x =
      M (matrixModuleAction (fun s i => (E s i : ℝ)) x)) (x : I → U) :
    CircleFourier.character (subspaceArrayFunctional U (fun i a => (frequency i a : ℝ)) x : CircleFourier.Circle) =
      subspaceArrayCharacter U (T.transpose * frequency)
        (QuotientAddGroup.mk' (subspaceArrayIntegerLattice S U)
          ((d : ℝ)⁻¹ • matrixModuleAction (fun s i => (E s i : ℝ)) x)) := by
  rw [subspaceArrayCharacter_mk]
  exact congrArg (fun t : ℝ => CircleFourier.character (t : CircleFourier.Circle))
    (integer_section_functional_factor U E T d hd hT frequency M hfactor x)

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped Matrix

theorem integer_section_polynomial_character {K S J : Type*}
    [Fintype K] [Fintype S] [Fintype J]
    (U : Submodule ℝ (J → ℝ)) (h : ℕ) (site : S → K → ℤ)
    (T : Matrix (BoundedCoefficientExponent K h) S ℤ) (d : ℕ) (hd : 0 < d)
    (hT : ∀ x : BoundedCoefficientExponent K h → U,
      matrixModuleAction (fun s i => (boundedSiteMatrix h site s i : ℝ))
        (matrixModuleAction (fun i s => (T i s : ℝ))
          (matrixModuleAction (fun s i => (boundedSiteMatrix h site s i : ℝ)) x)) =
        (d : ℝ) • matrixModuleAction (fun s i => (boundedSiteMatrix h site s i : ℝ)) x)
    (frequency : (K →₀ ℕ) → J → ℤ) (M : (S → U) →ₗ[ℝ] ℝ)
    (hfactor : ∀ p : VectorPolynomial K ℝ U, DegreeLE (1 : K → ℕ) h p →
      coefficientFunctional (fun e a => (frequency e a : ℝ)) (map U.subtype p) =
        M (siteEvaluation (fun s k => (site s k : ℝ)) p))
    (p : VectorPolynomial K ℝ U) (hp : DegreeLE (1 : K → ℕ) h p) :
    CircleFourier.character
        (coefficientFunctional (fun e a => (frequency e a : ℝ)) (map U.subtype p) : CircleFourier.Circle) =
      subspaceArrayCharacter U (T.transpose * Matrix.of (fun e a => frequency e.val a))
        (QuotientAddGroup.mk' (subspaceArrayIntegerLattice S U)
          ((d : ℝ)⁻¹ • siteEvaluation (fun s k => (site s k : ℝ)) p)) := by
  have hfun := coefficientFunctional_boundedArrayPolynomial U h
    (fun e a => (frequency e a : ℝ)) (fun e => coefficients p e.val)
  rw [boundedArrayPolynomial_reconstruct p hp] at hfun
  have hrow := integer_section_functional_factor U (boundedSiteMatrix h site) T d hd hT
    (Matrix.of (fun e a => frequency e.val a)) M
    (bounded_site_factorization_to_array U h site (fun e a => (frequency e a : ℝ)) M hfactor)
    (fun e => coefficients p e.val)
  rw [← siteEvaluation_bounded_coefficients site p hp] at hrow
  rw [subspaceArrayCharacter_mk]
  exact congrArg (fun t : ℝ => CircleFourier.character (t : CircleFourier.Circle)) (hfun.trans hrow)

end Erdos3.VectorPolynomial

end

end OAI
