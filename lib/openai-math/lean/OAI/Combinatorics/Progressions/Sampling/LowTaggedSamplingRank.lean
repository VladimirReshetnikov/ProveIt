/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Geometry.LowTaggedCoordinateRestriction
import OAI.Combinatorics.Progressions.Polynomial.PiCoordinatePolynomialCoefficients

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MvPolynomial
open scoped BigOperators

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)]

noncomputable def lowTaggedRetained (d : ℕ)
    (W : ∀ j, Submodule ℝ (J j → ℝ)) (h : Fin d) :
    Submodule ℝ (Fin (Fintype.card (LowTaggedIndex J d)) → ℝ) :=
  if hm : h.val < m then
    (W ⟨h.val, hm⟩).map (lowTaggedEmbedding J d ⟨h.val, hm⟩ (by exact Nat.succ_le_of_lt h.isLt))
  else ⊥

variable {X : Type*}

noncomputable def lowTaggedTopPolynomial (d : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) :
    VectorPolynomial X ℝ (Fin (Fintype.card (LowTaggedIndex J d)) → ℝ) :=
  ofCoordinates (R := ℝ) (Pi.basisFun ℝ _)
    (fun i => homogeneousComponent (lowTaggedWeight J d i) (lowTaggedPolynomial J d poly i))

theorem lowTaggedTopPolynomial_coeff_apply (d : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (α : X →₀ ℕ) (i : Fin (Fintype.card (LowTaggedIndex J d))) :
    coefficients (lowTaggedTopPolynomial J d poly) α i =
      if α.degree = lowTaggedWeight J d i then
        coefficients (poly (lowTaggedIndex J d i).1) α (lowTaggedIndex J d i).2 else 0 := by
  rw [lowTaggedTopPolynomial, coefficients_ofCoordinates_pi_apply,
    coeff_homogeneousComponent, lowTaggedPolynomial_coeff]

theorem lowTaggedTopPolynomial_coeff_of_degree (d : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (j : Fin m) (hj : j.val + 1 ≤ d) (α : X →₀ ℕ)
    (hα : α.degree = j.val + 1) :
    coefficients (lowTaggedTopPolynomial J d poly) α =
      lowTaggedEmbedding J d j hj (coefficients (poly j) α) := by
  classical
  funext i
  rw [lowTaggedTopPolynomial_coeff_apply]
  by_cases hi : (lowTaggedIndex J d i).1 = j
  · obtain ⟨k, hk⟩ := lowTaggedSlot_eq_of_tag J d j hj i hi
    subst i
    rw [lowTaggedEmbedding_apply_slot]
    simp only [lowTaggedWeight, lowTaggedIndex_slot, hα, ite_true]
    rw [lowTaggedIndex_slot]
  · rw [lowTaggedEmbedding_apply_of_ne J d j hj _ i hi]
    have hne : α.degree ≠ lowTaggedWeight J d i := by
      intro he
      apply hi
      apply Fin.ext
      unfold lowTaggedWeight at he
      omega
    simp only [hne, ite_false]

theorem lowTaggedTopPolynomial_row_layer (d : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (j : Fin m) (hj : j.val + 1 ≤ d)
    (a : Fin (Fintype.card (LowTaggedIndex J d)) → ℤ) :
    homogeneousComponent (j.val + 1)
        (integerRowPolynomial a (lowTaggedTopPolynomial J d poly)) =
      homogeneousComponent (j.val + 1)
        (integerRowPolynomial (fun k => a (lowTaggedSlot J d j hj k)) (poly j)) := by
  classical
  ext α
  simp only [coeff_homogeneousComponent]
  split
  · rename_i hα
    rw [integerRowPolynomial_coeff, integerRowPolynomial_coeff,
      lowTaggedTopPolynomial_coeff_of_degree J d poly j hj α hα]
    exact lowTaggedEmbedding_pairing J d j hj (fun i => (a i : ℝ)) _
  · rfl

theorem lowTaggedTopPolynomial_hasLayerSamplingRank (d : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (W : ∀ j, Submodule ℝ (J j → ℝ)) (T : X → ℝ) (R : ℝ)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) T R (W j) (poly j))
    (h : Fin d) :
    HasLayerSamplingRank (h.val + 1) T R (lowTaggedRetained J d W h)
      (lowTaggedTopPolynomial J d poly) := by
  classical
  intro a ha hw
  by_cases hm : h.val < m
  · let j : Fin m := ⟨h.val, hm⟩
    have hj : j.val + 1 ≤ d := by dsimp [j]; omega
    obtain ⟨w, hw⟩ := hw
    have hwmem : w.val ∈ (W j).map (lowTaggedEmbedding J d j hj) := by
      simpa only [lowTaggedRetained, dite_eq_left hm] using w.property
    obtain ⟨v, hv, he⟩ := Submodule.mem_map.mp hwmem
    have hpair : ∃ v : W j,
        (∑ k, (a (lowTaggedSlot J d j hj k) : ℝ) * v.val k) ≠ 0 := by
      refine ⟨⟨v, hv⟩, ?_⟩
      change (∑ k, (a (lowTaggedSlot J d j hj k) : ℝ) * v k) ≠ 0
      rw [← lowTaggedEmbedding_pairing J d j hj (fun i => (a i : ℝ)) v, he]
      exact hw
    have hn := hrank j (fun k => a (lowTaggedSlot J d j hj k))
      (fun k => ha _) hpair
    rw [lowTaggedTopPolynomial_row_layer J d poly j hj]
    exact hn
  · obtain ⟨w, hw⟩ := hw
    have hwzero : w.val = 0 := by
      have := w.property
      simpa only [lowTaggedRetained, dite_eq_right hm, Submodule.mem_bot] using this
    simp only [hwzero, Pi.zero_apply, mul_zero, Finset.sum_const_zero, ne_eq,
      not_true_eq_false] at hw

theorem lowTaggedTopPolynomial_coeff_mem_iSup (d : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (W : ∀ j, Submodule ℝ (J j → ℝ))
    (hcoeff : ∀ j α, α ≠ 0 → coefficients (poly j) α ∈ W j)
    (α : X →₀ ℕ) :
    coefficients (lowTaggedTopPolynomial J d poly) α ∈
      ⨆ h : Fin d, lowTaggedRetained J d W h := by
  classical
  by_cases hs : ∃ i, α.degree = lowTaggedWeight J d i
  · obtain ⟨i, hi⟩ := hs
    let j := (lowTaggedIndex J d i).1
    have hj : j.val + 1 ≤ d := lowTaggedIndex_property J d i
    let h : Fin d := ⟨j.val, by omega⟩
    have hα : α.degree = j.val + 1 := hi
    have hα0 : α ≠ 0 := by
      intro he
      subst α
      simp at hα
    apply Submodule.mem_iSup_of_mem h
    rw [lowTaggedTopPolynomial_coeff_of_degree J d poly j hj α hα]
    have heq : lowTaggedRetained J d W h =
        (W j).map (lowTaggedEmbedding J d j hj) := by
      simp only [lowTaggedRetained, h, dite_eq_left j.isLt]
    rw [heq]
    exact Submodule.mem_map.mpr ⟨_, hcoeff j α hα0, rfl⟩
  · have hz : coefficients (lowTaggedTopPolynomial J d poly) α = 0 := by
      funext i
      rw [lowTaggedTopPolynomial_coeff_apply]
      simp only [show α.degree ≠ lowTaggedWeight J d i from fun he => hs ⟨i, he⟩,
        ite_false, Pi.zero_apply]
    rw [hz]
    exact Submodule.zero_mem _

end Erdos3.VectorPolynomial

end

end OAI
