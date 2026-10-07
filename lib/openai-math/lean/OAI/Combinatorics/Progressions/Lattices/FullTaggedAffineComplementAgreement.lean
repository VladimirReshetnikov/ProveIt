import OAI.Combinatorics.Progressions.Linear.RationalTagProjectionComplement

namespace OAI

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial _root_.OAI.MvPolynomial

variable {m : ℕ} {X : Type*} (J : Fin m → Type*) [∀ j, Fintype (J j)]

theorem fullTaggedAffineMapChart_eval_eq_of_complement
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) (c : ∀ j, J j → ℝ)
    (x : X ⊕ (Σ j, J j) → ℝ)
    (hvalue : ∀ j, ((LinearMap.id : (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) - P j) (fun a => x (Sum.inr ⟨j, a⟩)) = c j)
    (hconstant : ∀ j, ((LinearMap.id : (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) - P j) (c j) = c j) :
    (fun v => MvPolynomial.eval x (fullTaggedAffineMapChart J P c v)) = x := by
  have hfixed : ∀ j y, y ∈ LinearMap.ker
      ((LinearMap.id : (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) - P j) → P j y = y := by
    intro j y hy
    change y - P j y = 0 at hy
    exact (sub_eq_zero.mp hy).symm
  apply fullTaggedAffineMapChart_eval_eq_of_quotient J P c
    (fun j => LinearMap.ker ((LinearMap.id : (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) - P j)) hfixed
    (fun j => (LinearMap.id : (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) - P j) (fun _ => rfl) x
  intro j
  rw [hvalue j, hconstant j]

theorem fullTaggedAffineMatrixChart_eval_eq_of_complement
    (P : ∀ j, Matrix (J j) (J j) ℚ) (c : ∀ j, J j → ℝ)
    (x : X ⊕ (Σ j, J j) → ℝ)
    (hvalue : ∀ j, rationalTagProjectionComplement (P j)
      (fun a => x (Sum.inr ⟨j, a⟩)) = c j)
    (hconstant : ∀ j, rationalTagProjectionComplement (P j) (c j) = c j) :
    (fun v => MvPolynomial.eval x
      (fullTaggedAffineMapChart J (fullTaggedRealMatrixProjection J P) c v)) = x := by
  exact fullTaggedAffineMapChart_eval_eq_of_complement J
    (fullTaggedRealMatrixProjection J P) c x hvalue hconstant

theorem fullTaggedAffineMatrixChart_eval_eq_of_anchor
    (P : ∀ j, Matrix (J j) (J j) ℚ) (c anchor : ∀ j, J j → ℝ)
    (x : X ⊕ (Σ j, J j) → ℝ)
    (hdisplacement : ∀ j, rationalTagProjectionComplement (P j)
      ((fun a => x (Sum.inr ⟨j, a⟩)) - anchor j) = 0)
    (hanchor : ∀ j, rationalTagProjectionComplement (P j) (anchor j) = c j)
    (hconstant : ∀ j, rationalTagProjectionComplement (P j) (c j) = c j) :
    (fun v => MvPolynomial.eval x
      (fullTaggedAffineMapChart J (fullTaggedRealMatrixProjection J P) c v)) = x := by
  apply fullTaggedAffineMatrixChart_eval_eq_of_complement J P c x ?_ hconstant
  intro j
  have h := hdisplacement j
  rw [map_sub, sub_eq_zero, hanchor j] at h
  exact h

theorem fullTaggedAffineMatrixChart_eval_eq_of_retraction_anchor
    (P : ∀ j, Matrix (J j) (J j) ℚ) (V : ∀ j, Submodule ℚ (J j → ℚ))
    (hrange : ∀ j, LinearMap.range (fullTaggedRealMatrixProjection J P j) =
      realRationalCoordinateSpan (V j))
    (hfix : ∀ j y, y ∈ realRationalCoordinateSpan (V j) →
      fullTaggedRealMatrixProjection J P j y = y)
    (anchor : ∀ j, J j → ℝ) (x : X ⊕ (Σ j, J j) → ℝ)
    (hdisplacement : ∀ j, rationalTagProjectionComplement (P j)
      ((fun a => x (Sum.inr ⟨j, a⟩)) - anchor j) = 0) :
    (fun v => MvPolynomial.eval x
      (fullTaggedAffineMapChart J (fullTaggedRealMatrixProjection J P)
        (fun j => rationalTagProjectionComplement (P j) (anchor j)) v)) = x := by
  apply fullTaggedAffineMatrixChart_eval_eq_of_anchor J P _ anchor x
    hdisplacement (fun _ => rfl)
  intro j
  exact rationalTagProjectionComplement_idempotent (P j) (V j)
    (hrange j) (hfix j) (anchor j)

end Erdos3.VectorPolynomial

end

end OAI
