import GowersSzemeredi.Proofs13EndpointAdditiveCollision

/-! Finite additive correction with explicit constants. If the addition
failure rate is below 1/6, the modal increment map is a homomorphism at
distance at most theta/(1-2theta), hence at most 2theta. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

private theorem endpointError_add {A H : Type*} [Fintype A] [Add H] [DecidableEq H]
    (u₁ u₂ v₁ v₂ : A → H) :
    endpointError (fun x => u₁ x + u₂ x) (fun x => v₁ x + v₂ x) ≤
      endpointError u₁ v₁ + endpointError u₂ v₂ := by
  unfold endpointError
  rw [← Finset.expect_add_distrib]
  apply Finset.expect_le_expect
  intro x _
  by_cases h₁ : u₁ x = v₁ x <;> by_cases h₂ : u₂ x = v₂ x <;>
    by_cases hs : u₁ x + u₂ x = v₁ x + v₂ x <;> simp_all

theorem endpointCorrectedMap_add {A H : Type*} [Fintype A] [AddCommGroup A]
    [Fintype H] [AddCommGroup H] [DecidableEq H] (u : A → H)
    (hsmall : endpointAdditiveFailure u < 1 / 6) (x x' : A) :
    endpointCorrectedMap u (x + x') = endpointCorrectedMap u x + endpointCorrectedMap u x' := by
  let v := endpointCorrectedMap u
  have hcocycle : (fun y => endpointIncrement u x (x' + y) + endpointIncrement u x' y) =
      endpointIncrement u (x + x') := by
    funext y
    unfold endpointIncrement
    rw [add_assoc]
    abel
  have hshift : endpointError (fun y => endpointIncrement u x (x' + y)) (fun _ => v x) ≤
      2 * endpointAdditiveFailure u := by
    have he := endpointError_equiv (Equiv.addLeft x') (endpointIncrement u x) (fun _ => v x)
    exact he.trans_le (endpointCorrectedMap_local_error u x)
  have hsum := endpointError_add (fun y => endpointIncrement u x (x' + y)) (endpointIncrement u x')
    (fun _ => v x) (fun _ => v x')
  rw [hcocycle] at hsum
  have htriangle := endpointError_triangle (fun _ : A => v (x + x')) (endpointIncrement u (x + x'))
    (fun _ => v x + v x')
  rw [endpointError_symm (fun _ : A => v (x + x')) (endpointIncrement u (x + x'))] at htriangle
  have hlocal := endpointCorrectedMap_local_error u (x + x')
  have hlocal' := endpointCorrectedMap_local_error u x'
  by_contra hne
  have hc : endpointError (fun _ : A => v (x + x')) (fun _ => v x + v x') = 1 := by
    rw [endpointError_const, if_neg hne]
  rw [hc] at htriangle
  nlinarith only [htriangle, hsum, hshift, hlocal, hlocal', hsmall]

theorem endpointCorrectedMap_distance_bound {A H : Type*} [Fintype A] [AddCommGroup A]
    [Fintype H] [AddCommGroup H] [DecidableEq H] (u : A → H) :
    (1 - 2 * endpointAdditiveFailure u) * endpointError u (endpointCorrectedMap u) ≤
      endpointAdditiveFailure u := by
  let v := endpointCorrectedMap u
  have hrow (x : A) :
      (1 - 2 * endpointAdditiveFailure u) * (if u x = v x then (0 : Real) else 1) ≤
        endpointError (endpointIncrement u x) (fun _ => u x) := by
    by_cases he : u x = v x
    · simp only [if_pos he, mul_zero]
      exact endpointError_nonneg _ _
    · have ht := endpointError_triangle (fun _ : A => u x) (endpointIncrement u x) (fun _ => v x)
      rw [endpointError_const, if_neg he, endpointError_symm (fun _ : A => u x)] at ht
      have hl := endpointCorrectedMap_local_error u x
      simp only [if_neg he, mul_one]
      linarith only [ht, hl]
  have hrows : (𝔼 x : A, endpointError (endpointIncrement u x) (fun _ => u x)) = endpointAdditiveFailure u := by
    unfold endpointAdditiveFailure endpointError
    rw [endpoint_expect_prod]
    apply Finset.expect_congr rfl
    intro x _
    apply Finset.expect_congr rfl
    intro y _
    simp only [endpointIncrement, sub_eq_iff_eq_add]
  have ht := Finset.expect_le_expect (fun x (_ : x ∈ (Finset.univ : Finset A)) => hrow x)
  rw [← Finset.mul_expect, hrows] at ht
  exact ht

theorem endpoint_additive_correction {A H : Type*} [Fintype A] [AddCommGroup A]
    [Fintype H] [AddCommGroup H] [DecidableEq H] (u : A → H)
    (hsmall : endpointAdditiveFailure u < 1 / 6) :
    ∃ v : A →+ H, endpointError u v ≤ endpointAdditiveFailure u / (1 - 2 * endpointAdditiveFailure u) ∧
      endpointError u v ≤ 2 * endpointAdditiveFailure u := by
  let v : A →+ H := AddMonoidHom.mk' (endpointCorrectedMap u) (endpointCorrectedMap_add u hsmall)
  have hd : 0 < 1 - 2 * endpointAdditiveFailure u := by linarith only [hsmall]
  have ht := endpointCorrectedMap_distance_bound u
  have hbound : endpointError u v ≤ endpointAdditiveFailure u / (1 - 2 * endpointAdditiveFailure u) := by
    apply (le_div_iff₀ hd).mpr
    change endpointError u (endpointCorrectedMap u) * (1 - 2 * endpointAdditiveFailure u) ≤ _
    nlinarith only [ht]
  refine ⟨v, hbound, hbound.trans ?_⟩
  apply (div_le_iff₀ hd).mpr
  have hpos : 0 ≤ endpointAdditiveFailure u := endpointError_nonneg _ _
  have hh : 0 ≤ endpointAdditiveFailure u * (1 - 4 * endpointAdditiveFailure u) :=
    mul_nonneg hpos (by linarith only [hsmall])
  nlinarith only [hh]

end LeanProofs.GowersSzemeredi
