import GowersSzemeredi.Proofs16AffineTupleRows

/-! A domain refinement retains a dense set of rows after translation.
The variable maps stay unchanged; their offsets become fixed frequencies. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Retain density and actual row geometry on any smaller quarter domain. -/
theorem dense_affine_bohr_refinement {N Q : Nat} [NeZero N] [NeZero Q]
    {κ : Type*} [Fintype κ] (A : Finset (ZMod N × ZMod N))
    (W F Gamma S : Finset (ZMod N)) (L : κ → ZMod N → ZMod N)
    (a : ZMod N) {sigma eta alpha : Real} (hsigma : 0 ≤ sigma)
    (heta : 0 ≤ eta) (ha : 0 < alpha) (hQ : 4 ≤ sigma * Q)
    (hW : W ⊆ bohr Gamma (sigma / 4))
    (hS : bohr S (sigma / 4) ⊆ bohr Gamma (sigma / 4))
    (hL : ∀ j, IsFreimanLinearOn (bohr Gamma sigma) (L j))
    (hcard : alpha * N ≤ W.card) (hgeom : tupleRowGeometry A W F L a eta) :
    ∃ (t : ZMod N) (V F' : Finset (ZMod N)),
      V.Nonempty ∧ V ⊆ bohr S (sigma / 4) ∧
      alpha * ((bohr S (sigma / 4)).card : Real) ≤ V.card ∧
      (alpha / (Q : Real)^S.card) * N ≤ V.card ∧
      F ⊆ F' ∧ F'.card ≤ F.card + Fintype.card κ ∧
      (∀ x ∈ V, t + x ∈ W) ∧
      tupleRowGeometry A V F' L (a + t) (eta / 2) := by
  have hquarter : bohr Gamma (sigma / 4) ⊆ bohr Gamma sigma :=
    bohr_mono_radius Gamma (by linarith)
  obtain ⟨t, V, c, hVne, hV, hrelative, hVW, haff⟩ :=
    exists_dense_affine_cluster (bohr Gamma sigma) W (bohr S (sigma / 4)) L
      (hW.trans hquarter) (hS.trans hquarter)
      ⟨0, zero_mem_bohr S (by positivity)⟩ hL ha hcard
  refine ⟨t, V, F ∪ Finset.univ.image c, hVne, hV, hrelative, ?_,
    Finset.subset_union_left, affine_fixed_frequencies_card_le F c, hVW,
    hgeom.affine_recenter heta c hVW haff⟩
  apply bohr_cluster_density_lower V S Q ha.le (show 2 ≤ (sigma / 2) * Q by linarith)
  simpa only [div_div, show (2 : Real) * 2 = 4 by norm_num] using hrelative

end LeanProofs.GowersSzemeredi
