import OAI.Combinatorics.Progressions.Linear.FastKernelReabsorptionControl
import OAI.Combinatorics.Progressions.Linear.FormalKernelAbsorption

namespace OAI

section

namespace Erdos3

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

namespace VectorPolynomial

variable {σ κ ι K L : Type*} [Fintype κ] [AddCommGroup K] [Module ℝ K]
  [LieRing L] [LieAlgebra ℚ L]

theorem basisPolynomialLift_bound_of_coordinate_bound (b : Basis κ ℝ K)
    (S : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (e : Basis ι ℝ (ℝ ⊗[ℚ] L))
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) (M A τ : ℝ) (hM : 0 ≤ M)
    (hS : ∀ k, CoefficientBound e T M (S k)) (x : K)
    (hx : ‖b.equivFun x‖ ≤ A / τ) :
    CoefficientBound e T ((Fintype.card κ : ℝ) * M * A / τ)
      (basisPolynomialLift b S x) := by
  apply (basisPolynomialLift_coefficientBound b S e T M hS x).mono e T hT
  calc
    (Fintype.card κ : ℝ) * M * ‖b.equivFun x‖ ≤
        (Fintype.card κ : ℝ) * M * (A / τ) :=
      mul_le_mul_of_nonneg_left hx (mul_nonneg (Nat.cast_nonneg _) hM)
    _ = _ := by ring

theorem basisPolynomialLift_reabsorption_bound (b : Basis κ ℝ K)
    (S : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (e : Basis ι ℝ (ℝ ⊗[ℚ] L))
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) (M N A τ : ℝ) (hM : 0 ≤ M)
    (hS : ∀ k, CoefficientBound e T M (S k))
    (small : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hsmall : CoefficientBound e T (N / τ) small)
    (x : K) (hx : ‖b.equivFun x‖ ≤ A / τ) :
    CoefficientBound e T ((N + (Fintype.card κ : ℝ) * M * A) / τ)
      (small + basisPolynomialLift b S x) := by
  have h := basisPolynomialLift_bound_of_coordinate_bound b S e T hT M A τ hM hS x hx
  have hsum := hsmall.sub e T (h.neg e T)
  rw [sub_neg_eq_add] at hsum
  convert hsum using 1
  ring

theorem basisPolynomialLift_reabsorption_grid (b : Basis κ ℝ K)
    (R : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (e : Basis ι ℝ (ℝ ⊗[ℚ] L))
    (l m n : ℕ) (hR : ∀ k, CoefficientGrid e m (R k))
    (rational : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hrational : CoefficientGrid e n rational)
    (x : K) (hx : b.equivFun x ∈ realDenominatorGrid l) :
    CoefficientGrid e (n * (m * l)) (rational + basisPolynomialLift b R x) := by
  have h := basisPolynomialLift_coefficientGrid b R e l m hR x hx
  intro α
  have hsum := realDenominatorGrid_sub_product n (m * l)
    (fun i => e.repr (coefficients rational α) i)
    (-(fun i => e.repr (coefficients (basisPolynomialLift b R x) α) i))
    (hrational α) (realDenominatorGrid_neg (m * l) (h α))
  simp only [sub_neg_eq_add] at hsum
  simp only [map_add, Finsupp.add_apply]
  exact hsum

end VectorPolynomial

namespace NilpotentLieBCHGroup

variable {σ κ ι K L : Type*} [Fintype κ] [AddCommGroup K] [Module ℝ K]
  [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ (ℝ ⊗[ℚ] L) (ℝ ⊗[ℚ] L) s = ⊥}

theorem formal_basis_lift_reabsorption_control (b : Basis κ ℝ K)
    (V : Submodule ℝ (ℝ ⊗[ℚ] L)) (P : PolynomialGroup σ hnil)
    (S R : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (small rational : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (k a c : σ → K)
    (hSR : PolynomialLiftSystemMod (V.restrictScalars ℚ) P S R)
    (hsystem : PolynomialDerivativeSystemMod (V.restrictScalars ℚ) P small rational
      (fun i => basisPolynomialLift b S (k i)))
    (e : Basis ι ℝ (ℝ ⊗[ℚ] L)) (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (M N A : ℝ) (hM : 0 ≤ M)
    (hS : ∀ z, CoefficientBound e T M (S z))
    (hsmall : ∀ i, CoefficientBound e T (N / T i) (small i))
    (ha : ∀ i, ‖b.equivFun (a i)‖ ≤ A / T i)
    (l m n : ℕ) (hR : ∀ z, CoefficientGrid e m (R z))
    (hrational : ∀ i, CoefficientGrid e n (rational i))
    (hc : ∀ i, b.equivFun (c i) ∈ realDenominatorGrid l) :
    let S' := basisPolynomialLift b S
    let R' := basisPolynomialLift b R
    let small' := fun i => small i + S' (a i)
    let rational' := fun i => rational i + R' (c i)
    PolynomialLiftSystemMod (V.restrictScalars ℚ) P S' R' ∧
      PolynomialDerivativeSystemMod (V.restrictScalars ℚ) P small' rational'
        (fun i => S' (k i - a i - c i)) ∧
      (∀ i, CoefficientBound e T ((N + (Fintype.card κ : ℝ) * M * A) / T i) (small' i)) ∧
      ∀ i, CoefficientGrid e (n * (m * l)) (rational' i) := by
  intro S' R' small' rational'
  have hSR' := hSR.extend_basis b V P S R
  refine ⟨hSR', ?_, ?_, ?_⟩
  · exact PolynomialDerivativeSystemMod.absorb (V.restrictScalars ℚ) P
      S'.toAddMonoidHom R'.toAddMonoidHom small rational k a c hSR' hsystem
  · intro i
    exact basisPolynomialLift_reabsorption_bound b S e T hT M N A (T i) hM hS
      (small i) (hsmall i) (a i) (ha i)
  · intro i
    exact basisPolynomialLift_reabsorption_grid b R e l m n hR
      (rational i) (hrational i) (c i) (hc i)

end NilpotentLieBCHGroup

end Erdos3

end

end OAI
