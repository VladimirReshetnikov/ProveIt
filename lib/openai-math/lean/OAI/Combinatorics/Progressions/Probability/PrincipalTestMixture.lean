import OAI.Combinatorics.Progressions.Estimates.AllocatedEnormousProfiles
import OAI.Combinatorics.Progressions.Estimates.ComplexTestScaling

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem principal_mixed_test_comparison {D α V : Type*}
    [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
    (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
    (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j) (m : ℕ) [NeZero m] (hm : 0 < m)
    (hsize : ∀ j, (Fintype.card α+1)*m ≤ L j) (s : Finset V)
    (c : PrincipalIntegerTuples B h α L → V → ℝ)
    (a : PrincipalIntegerTuples B h α L → V → ℂ)
    (b : (PrincipalTupleIndex B h → Option α → ZMod m) → V → ℂ)
    (T : (PrincipalTupleIndex B h → Option α → ZMod m) → (V → ℂ) → ℂ)
    (hT : ∀ r z ψ, T r (fun v => z * ψ v) = z * T r ψ)
    (M ε : (PrincipalTupleIndex B h → Option α → ZMod m) → ℝ)
    (hM : ∀ r, 0 < M r) (hb : ∀ r v, v ∈ s → ‖b r v‖ ≤ M r)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hc : ∀ y, (principalTupleWeights (α := α) B h L hL).weight y ≠ 0 → ∀ v ∈ s, 0 ≤ c y v)
    (hmass : ∀ y, (principalTupleWeights (α := α) B h L hL).weight y ≠ 0 → (∑ v ∈ s, c y v) ≤ 1)
    (hspatial : ∀ y, (principalTupleWeights (α := α) B h L hL).weight y ≠ 0 →
      ∀ v ∈ s, ‖a y v - b (principalResidueLabel m y) v‖ ≤ δ)
    (hcoeff : ∀ r ψ, (∀ v ∈ s, ‖ψ v‖ ≤ 1) →
      ‖(principalResidueWeights B h L hL m hm r hsize).complexMean
        (fun y => ∑ v ∈ s, (c y v : ℂ) * ψ v) - T r ψ‖ ≤ ε r)
    (φ : V → ℂ) (hφ : ∀ v ∈ s, ‖φ v‖ ≤ 1) :
    let p := principalTupleWeights (α := α) B h L hL
    let q := p.fiberLaw (principalResidueLabel m)
    ‖p.complexMean (fun y => ∑ v ∈ s, (c y v : ℂ) * a y v * φ v) -
      q.complexMean (fun r => T r (fun v => b r v * φ v))‖ ≤ δ + q.mean (fun r => M r * ε r) := by
  dsimp only
  let p := principalTupleWeights (α := α) B h L hL
  let q := p.fiberLaw (principalResidueLabel m)
  have hfirst := finiteMean_spatial_error_of_mass p s c a
    (fun y => b (principalResidueLabel m y)) φ hδ hc hmass hφ hspatial
  have hmid : p.complexMean (fun y => ∑ v ∈ s, (c y v : ℂ) * b (principalResidueLabel m y) v * φ v) =
      q.complexMean (fun r => (principalResidueWeights B h L hL m hm r hsize).complexMean
        (fun y => ∑ v ∈ s, (c y v : ℂ) * (b r v * φ v))) := by
    simpa only [mul_assoc] using principalTuple_complex_disintegrate B h L hL m hm hsize
      (fun r y => ∑ v ∈ s, (c y v : ℂ) * b r v * φ v)
  rw [hmid] at hfirst
  have hsecond := q.norm_complexMean_sub_le _ _ (fun r => M r * ε r) (fun r _ =>
    finiteMean_density_test_bound (principalResidueWeights B h L hL m hm r hsize) s c
      (T r) (hT r) (hcoeff r) (hM r) (fun v => b r v * φ v) (by
        intro v hv
        rw [norm_mul]
        exact (mul_le_mul (hb r v hv) (hφ v hv) (norm_nonneg _) (hM r).le).trans_eq (mul_one _)))
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hfirst hsecond)

end Erdos3

end

end OAI
