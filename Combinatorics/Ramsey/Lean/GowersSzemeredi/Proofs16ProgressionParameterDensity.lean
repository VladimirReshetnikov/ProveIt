import GowersSzemeredi.Proofs16ProperBohrProgression
import GowersSzemeredi.Proofs16BohrFourTerm

/-! A dense parameter set retains its density on a translate of a proper
progression whose fourfold sums remain in the original Bohr domain. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Averaging localizes a dense set on a translated proper progression.
The mass bound is relative to the progression, with an explicit ambient
bound as well. No dilation of the progression is assumed proper. -/
theorem dense_parameters_on_proper_progression {N : Nat} [NeZero N]
    (V T : Finset (ZMod N)) {nu rho w : Real}
    (hnu : 0 < nu) (hV : nu * N ≤ (V.card : Real))
    (hrho : 0 < rho) (hw : 0 ≤ w) (hwidth : Real.exp (-w) ≤ rho) :
    ∃ (Q : OAI.Erdos3.BohrProgression.CyclicCenteredGAP N)
      (t : ZMod N) (W : Finset (ZMod N)),
      Q.rank ≤ T.card + 1 ∧ Q.Proper ∧ Q.carrier ⊆ bohr T (rho / 4) ∧
      W.Nonempty ∧ W ⊆ Q.carrier ∧
      nu * (Q.carrier.card : Real) ≤ (W.card : Real) ∧
      nu * Real.exp (-(((T.card : Real) + 1) * w + 10 * ((T.card : Real) + 1)^2)) * N ≤
        (W.card : Real) ∧
      (∀ x ∈ W, t + x ∈ V) ∧
      ∀ x₁ ∈ Q.carrier, ∀ x₂ ∈ Q.carrier, ∀ x₃ ∈ Q.carrier, ∀ x₄ ∈ Q.carrier,
        x₁ + x₂ - x₃ - x₄ ∈ bohr T rho := by
  obtain ⟨Q, hQrank, hQproper, hQsub, hQcard⟩ :=
    exists_proper_progression_in_bohr T hrho hw hwidth
  obtain ⟨t, ht⟩ := exists_dense_localTranslate V Q.carrier hV
  let W := localTranslateCoordinates V Q.carrier t
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hQpos : (0 : Real) < Q.carrier.card :=
    (mul_pos (Real.exp_pos _) hN).trans_le hQcard
  have hW : W.Nonempty := by
    apply Finset.card_pos.mp
    exact_mod_cast (mul_pos hnu hQpos).trans_le ht
  refine ⟨Q, t, W, hQrank, hQproper, hQsub, hW,
    Finset.filter_subset _ _, ht, ?_, ?_, ?_⟩
  · have h := mul_le_mul_of_nonneg_left hQcard hnu.le
    rw [← mul_assoc] at h
    exact h.trans ht
  · intro x hx
    exact (Finset.mem_filter.mp hx).2
  · intro x₁ h₁ x₂ h₂ x₃ h₃ x₄ h₄
    exact bohr_four_term_mem T (hQsub h₁) (hQsub h₂) (hQsub h₃) (hQsub h₄)

/-- A normalized local Freiman map respects differences of quarter-radius
inputs, with every argument still in its declared domain. -/
theorem freiman_bohr_difference {N : Nat} [NeZero N] (T : Finset (ZMod N))
    (f : ZMod N → ZMod N) {rho : Real} (hrho : 0 ≤ rho)
    (hf : FreimanHom 2 (bohr T rho) f) (hf0 : f 0 = 0)
    {x y : ZMod N} (hx : x ∈ bohr T (rho / 4)) (hy : y ∈ bohr T (rho / 4)) :
    f (x - y) = f x - f y := by
  have hmono := bohr_mono_radius T (show rho / 4 ≤ rho by linarith)
  have hxy := bohr_mono_radius T (show rho / 4 + rho / 4 ≤ rho by linarith)
    (bohr_sub_radius T hx hy)
  have h := hf.isFreimanLinearOn (by decide) (x - y) y x 0
    hxy (hmono hy) (hmono hx) (zero_mem_bohr T hrho) (by ring)
  rw [hf0] at h
  linear_combination h

end LeanProofs.GowersSzemeredi
