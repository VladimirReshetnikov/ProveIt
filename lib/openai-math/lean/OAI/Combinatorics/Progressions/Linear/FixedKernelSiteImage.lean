import OAI.Combinatorics.Progressions.Estimates.MixedBooleanSiteValues

namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

theorem exists_matrix_factor_of_common_reconstruction {S J K I : Type*}
    [Fintype S] [Fintype J] [Fintype K] [Fintype I]
    (E₀ : Matrix S K ℝ) (E : Matrix S I ℝ) (B : Matrix S J ℝ) (T : Matrix J S ℝ)
    (h₀ : B * T * E₀ = E₀) (hE : B * T * E = E)
    (hs : Function.Surjective (Matrix.mulVec (T * E₀))) :
    ∃ R : Matrix K I ℝ, E₀ * R = E := by
  choose v hv using fun i : I => hs (fun j => (T * E) j i)
  let R : Matrix K I ℝ := fun k i => v i k
  have hr : (T * E₀) * R = T * E := by
    ext j i
    exact congrFun (hv i) j
  refine ⟨R, ?_⟩
  calc
    E₀ * R = (B * (T * E₀)) * R := by rw [← Matrix.mul_assoc, h₀]
    _ = B * ((T * E₀) * R) := Matrix.mul_assoc _ _ _
    _ = B * (T * E) := by rw [hr]
    _ = E := by rw [← Matrix.mul_assoc, hE]

theorem boundedSiteMatrix_fixed_kernel_factor {α K I : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] [Fintype I]
    (root₀ : K → ℤ) (D₀ : Matrix α K ℤ) (a : ℤ) (ha : a ≠ 0)
    (hperiod : integerScalarLattice α a ≤ D₀.mulVecLin.range)
    (h : ℕ) (root : I → ℤ) (D : Matrix α I ℤ) :
    ∃ R : Matrix (VectorPolynomial.BoundedCoefficientExponent K h)
        (VectorPolynomial.BoundedCoefficientExponent I h) ℝ,
      Matrix.of (fun s d => (VectorPolynomial.boundedSiteMatrix h (integerAffineCube root₀ D₀) s d : ℝ)) * R =
        Matrix.of (fun s d => (VectorPolynomial.boundedSiteMatrix h (integerAffineCube root D) s d : ℝ)) := by
  classical
  let B := boundedBooleanReconstructionMatrix α h
  let T := booleanJetExtractionMatrix (Subtype.val : BoundedBooleanJet α h → Finset α)
  let E₀ := VectorPolynomial.boundedSiteMatrix h (integerAffineCube root₀ D₀)
  let E := VectorPolynomial.boundedSiteMatrix h (integerAffineCube root D)
  let B' := Matrix.of (fun s j => (B s j : ℝ))
  let T' := Matrix.of (fun j s => (T j s : ℝ))
  let E₀' := Matrix.of (fun s d => (E₀ s d : ℝ))
  let E' := Matrix.of (fun s d => (E s d : ℝ))
  have h₀ : B' * T' * E₀' = E₀' := by
    ext s d
    have hz := congrArg (fun z : ℤ => (z : ℝ))
      (congrFun (congrFun (boundedBooleanReconstruction_siteMatrix root₀ D₀ h) s) d)
    simpa only [B', T', E₀', B, T, E₀, Matrix.mul_apply, Matrix.of_apply,
      Int.cast_sum, Int.cast_mul] using hz
  have hE : B' * T' * E' = E' := by
    ext s d
    have hz := congrArg (fun z : ℤ => (z : ℝ))
      (congrFun (congrFun (boundedBooleanReconstruction_siteMatrix root D h) s) d)
    simpa only [B', T', E', B, T, E, Matrix.mul_apply, Matrix.of_apply,
      Int.cast_sum, Int.cast_mul] using hz
  have hjet : T' * E₀' = Matrix.of (fun j d => (boundedCoefficientJetMatrix root₀ D₀ h
      (Subtype.val : BoundedBooleanJet α h → Finset α) j d : ℝ)) := by
    ext j d
    have hz := congrArg (fun z : ℤ => (z : ℝ))
      (congrFun (congrFun (booleanJetExtractionMatrix_mul_boundedSite root₀ D₀ h
        (Subtype.val : BoundedBooleanJet α h → Finset α)) j) d)
    simpa only [T', E₀', T, E₀, Matrix.mul_apply, Matrix.of_apply, Int.cast_sum, Int.cast_mul] using hz
  apply exists_matrix_factor_of_common_reconstruction E₀' E' B' T' h₀ hE
  rw [hjet]
  intro v
  obtain ⟨x, hx⟩ := matrixModuleAction_surjective_of_period (W := ℝ)
    (boundedCoefficientJetMatrix root₀ D₀ h (Subtype.val : BoundedBooleanJet α h → Finset α))
    (a ^ h) (pow_ne_zero _ ha)
    (boundedCoefficientJetMatrix_period root₀ D₀ a hperiod h
      (Subtype.val : BoundedBooleanJet α h → Finset α) Subtype.val_injective (fun j => j.property)) v
  refine ⟨x, ?_⟩
  ext j
  exact congrFun hx j

end Erdos3

end

end OAI
